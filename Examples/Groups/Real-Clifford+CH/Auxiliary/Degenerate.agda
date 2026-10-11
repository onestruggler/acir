------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of Figure 7 fails on improper words
--
-- `Gen N` admits the degenerate letters X_[a,a] and H_[a,a], which the
-- paper's G_N excludes.  X_[a,a] denotes the identity, as ε does; but
-- every rule of Figure 7 has distinct indices, so both sides of each
-- have no degenerate letter, and the number of degenerate letters of a
-- word is an invariant of the congruence (`deg-≈`).  Hence X_[a,a] is
-- not ≈ ε, and completeness stated for every word of `Gen N` is false
-- — at four basis vectors (`refute₄`) and at every width of P
-- (`refute`).  That is why Theorem 4.4 is stated for proper words
-- (Auxiliary.Syntactics.Proper): an unrestricted hypothesis would make
-- every theorem assuming it vacuous.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Degenerate where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin ; _≟_)
open import Data.Nat using (ℕ ; _+_ ; zero ; suc) renaming (_^_ to _^ℕ_)
open import Data.Nat.Properties using (+-identityʳ ; +-assoc)
open import Data.Product using (_,_ ; proj₂)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_ ; does)
open import Relation.Nullary.Decidable using (dec-true ; dec-false)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_ ; ~-reflexive ; Bits ; Op ; _≐_ ; Idₒ ; δb)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas using (eqB-sound)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB ; swapOp ; ⟦_⟧ᴳ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
  using (Gen ; −1[_] ; X[_,_] ; H[_,_] ; _G,_===_)
open _G,_===_

import Examples.Groups.Real-Clifford+CH.BackAndForth as BackAndForth
import Examples.Groups.Real-Clifford+CH.TwoQubit as TwoQubit

private
  variable
    N : ℕ
    u v : Word (Gen N)

------------------------------------------------------------------------
-- The number of degenerate letters

ind : Bool → ℕ
ind true  = 1
ind false = 0

degᵍ : Gen N → ℕ
degᵍ −1[ a ]    = 0
degᵍ X[ a , b ] = ind (does (a ≟ b))
degᵍ H[ a , b ] = ind (does (a ≟ b))

deg : Word (Gen N) → ℕ
deg [ g ]ʷ  = degᵍ g
deg ε       = 0
deg (u • v) = deg u + deg v

private
  dX : ∀ {a b : Fin N} → a ≢ b → deg (G.X a b) ≡ 0
  dX {a = a} {b} ne rewrite dec-false (a ≟ b) ne = Eq.refl

  dH : ∀ {a b : Fin N} → a ≢ b → deg (G.H a b) ≡ 0
  dH {a = a} {b} ne rewrite dec-false (a ≟ b) ne = Eq.refl

  sym≢ : ∀ {a b : Fin N} → a ≢ b → b ≢ a
  sym≢ ne e = ne (Eq.sym e)

  _⊕_ : ∀ {x y : ℕ} → x ≡ 0 → y ≡ 0 → x + y ≡ 0
  Eq.refl ⊕ Eq.refl = Eq.refl
  infixr 5 _⊕_

-- Both sides of every rule of Figure 7 are free of degenerate letters.
deg-lhs : N G, u === v → deg u ≡ 0
deg-lhs a1*             = Eq.refl
deg-lhs (a2 p)          = dX p ⊕ dX p
deg-lhs (a3 p)          = dH p ⊕ dH p
deg-lhs b1*             = Eq.refl
deg-lhs b4*             = Eq.refl
deg-lhs b6*             = Eq.refl
deg-lhs (c1 p)          = Eq.refl ⊕ dX p
deg-lhs (c5 p q r)      = dH q ⊕ dX r
deg-lhs (d2 p)          = Eq.refl ⊕ dH p
deg-lhs d3*             = Eq.refl
deg-lhs d4*             = Eq.refl
deg-lhs (e2* p)         = dH (sym≢ p) ⊕ dX p

deg-rhs : N G, u === v → deg v ≡ 0
deg-rhs a1*             = Eq.refl
deg-rhs (a2 p)          = Eq.refl
deg-rhs (a3 p)          = Eq.refl
deg-rhs b1*             = Eq.refl
deg-rhs b4*             = Eq.refl
deg-rhs b6*             = Eq.refl
deg-rhs (c1 p)          = dX p ⊕ Eq.refl
deg-rhs (c5 p q r)      = dX r ⊕ dH p
deg-rhs (d2 p)          = dH p ⊕ dX p
deg-rhs d3*             = Eq.refl
deg-rhs d4*             = Eq.refl
deg-rhs (e2* p)         = dX p ⊕ dH p

-- The congruence preserves the number.
deg-≈ : PB._≈_ (N G,_===_) u v → deg u ≡ deg v
deg-≈ PB.refl            = Eq.refl
deg-≈ (PB.sym e)         = Eq.sym (deg-≈ e)
deg-≈ (PB.trans e f)     = Eq.trans (deg-≈ e) (deg-≈ f)
deg-≈ (PB.cong e f)      = Eq.cong₂ _+_ (deg-≈ e) (deg-≈ f)
deg-≈ {u = (w • v) • t} PB.assoc = +-assoc (deg w) (deg v) (deg t)
deg-≈ PB.left-unit       = Eq.refl
deg-≈ {u = w • ε} PB.right-unit = +-identityʳ (deg w)
deg-≈ (PB.axiom a)       = Eq.trans (deg-lhs a) (Eq.sym (deg-rhs a))

-- So a degenerate letter is not ε.
X-not-ε : ∀ (a : Fin N) → ¬ PB._≈_ (N G,_===_) (G.X a a) ε
X-not-ε a e with Eq.trans (Eq.cong ind (Eq.sym (dec-true (a ≟ a) Eq.refl))) (deg-≈ e)
... | ()

------------------------------------------------------------------------
-- Yet it denotes the identity

swap-id : ∀ {n} (i : Bits n) → swapOp i i ≐ Idₒ
swap-id i x y with eqB x i in e
... | true  = Eq.cong (λ z → δb z y) (Eq.sym (eqB-sound x i e))
... | false = Eq.refl

-- At the width of P.
module _ (m : ℕ) where
  private
    module BG = BackAndForth (₃₊ m) (2 ^ℕ ₃₊ m G,_===_) (⟦_⟧ᴳ {₃₊ m})

  refute : ¬ (∀ {u t : Word (Gen (2 ^ℕ ₃₊ m))} → BG.⟦ u ⟧Y ~ BG.⟦ t ⟧Y →
              PB._≈_ (2 ^ℕ ₃₊ m G,_===_) u t)
  refute complete =
    X-not-ε a (complete {u = G.X a a} {t = ε} (~-reflexive {l = 0} Eq.refl (swap-id _)))
    where
    a : Fin (2 ^ℕ ₃₊ m)
    a = fin8 {m} ₀

-- At four basis vectors (two qubits), with TwoQubit's matrices.
refute₄ : ¬ (∀ {u t : Word (Gen 4)} → TwoQubit.BF.⟦ u ⟧Y ~ TwoQubit.BF.⟦ t ⟧Y →
             PB._≈_ (4 G,_===_) u t)
refute₄ complete = X-not-ε ₀ (complete {u = G.X ₀ ₀} {t = ε} (~-reflexive {l = 0} Eq.refl sw))
  where
  sw : proj₂ (TwoQubit.BF.⟦ G.X ₀ ₀ ⟧Y) ≐ Idₒ
  sw (false ∷ false ∷ []) y = Eq.refl
  sw (true  ∷ false ∷ []) y = Eq.refl
  sw (false ∷ true  ∷ []) y = Eq.refl
  sw (true  ∷ true  ∷ []) y = Eq.refl
