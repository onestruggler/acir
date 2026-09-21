------------------------------------------------------------------------
-- Presentations of groups
--
-- The equations of Item (a) of the Reidemeister–Schreier method
-- (Clément, Appendix A.3.2, the equations (DE-**))
--
-- The method's first family of obligations says that a letter of P is
-- recovered by running its image over the auxiliary generators through
-- the coset action, starting from the identity coset.  Reading the
-- table of Definition A.2 off, the four shapes give
--
--     (−1)_[a](−1)_[b]      ↦  ((−1)_[1](−1)_[a]) ((−1)_[1](−1)_[b])
--     (−1)_[c]X_[a,b]       ↦  ((−1)_[1](−1)_[c]) ((−1)_[1]X_[a,b])
--     X_[a,b]X_[c,d]        ↦  ((−1)_[u]X_[a,b]) ((−1)_[1]X_[c,d])
--     H_[a,b]H_[c,d]        ↦  (H_[a,b]H_[0,1]) (H_[0,1]H_[c,d])
--
-- (u being b, a or 1 according as a, b or neither is the index 1), and
-- each has to be derived from Figure 8.  This module does the first,
-- which needs only the sign equations: the two others are the paper's
-- (DE-ZX) and (DE-XX-k) and the last (DE-HH).
--
-- Only (20)–(22) are involved here, and they say that the signs form
-- the group of even-weight subsets: (21) is symmetry, (22) is that a
-- sign pair composes along a shared index, and (20) that a repeated
-- index cancels.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.DE (m : ℕ) where

open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

open import Presentation.Base as PB using ()

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (o₁)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx)

open PB (m P,_===_)
  using (_≈_ ; refl ; sym ; trans ; cong ; axiom ; assoc ; left-unit ; right-unit)

------------------------------------------------------------------------
-- (DE-ZZ)

-- A sign pair is the pair through the index 1: (22) composes along it
-- and (21) puts the shared index first.
DE-ZZ : ∀ (a b : Fin _) → zz a b ≈ zz o₁ a • zz o₁ b
DE-ZZ a b = trans (sym (axiom (r22 a o₁ b))) (cong (axiom (r21 a o₁)) refl)

-- The sign pair on the index 1 twice over is trivial: (21), (22), (20).
private
  zz-o² : ∀ (a : Fin _) → zz o₁ a • zz o₁ a ≈ ε
  zz-o² a = trans (cong (axiom (r21 o₁ a)) refl)
                  (trans (axiom (r22 a o₁ a)) (axiom (r20 a)))

  -- Routing a sign pair through the index 1.
  zz-route : ∀ (c a : Fin _) → zz o₁ c • zz o₁ a ≈ zz c a
  zz-route c a = trans (cong (axiom (r21 o₁ c)) refl) (axiom (r22 c o₁ a))

------------------------------------------------------------------------
-- (DE-ZX), where the indices allow (30)
--
-- (30) peels the sign of a mixed letter onto the first index of its X,
-- so both sides reduce to zx a a b and what is left is a sign identity.
-- It needs all three indices distinct, so this is the case where c is
-- neither a nor b and the index 1 is neither either.

DE-ZX : ∀ (c a b : Fin _) → (a≢b : a ≢ b) → c ≢ a → c ≢ b → o₁ ≢ a → o₁ ≢ b →
        zx c a b ≈ zz o₁ c • zx o₁ a b
DE-ZX c a b a≢b c≢a c≢b o≢a o≢b =
  trans (axiom (r30 c a b a≢b c≢a c≢b))
  (trans (cong (sym (zz-route c a)) refl)
  (trans assoc
         (cong refl (sym (axiom (r30 o₁ a b a≢b o≢a o≢b))))))

-- The case c = a: the two sign pairs cancel outright.
DE-ZX-fix : ∀ (a b : Fin _) → (a≢b : a ≢ b) → o₁ ≢ a → o₁ ≢ b →
            zx a a b ≈ zz o₁ a • zx o₁ a b
DE-ZX-fix a b a≢b o≢a o≢b = sym
  (trans (cong refl (axiom (r30 o₁ a b a≢b o≢a o≢b)))
  (trans (sym assoc)
  (trans (cong (zz-o² a) refl) left-unit)))

------------------------------------------------------------------------
-- Exchanging the two X indices of a mixed letter
--
-- Every case of (DE-ZX) that (30) does not reach — c the second index
-- of the X, or the index 1 one of the two — comes down to moving the
-- sign across an exchange of the X indices:
--
--     zx a a b  ≈  zz a b • zx b b a.
--
-- For consecutive indices Figure 8 gives it outright: (23) says the
-- sign pair is the square of the mixed letter, (29) that the letter
-- and its index-exchanged partner are inverse, and (33) rewrites that
-- partner.  For a general pair it is the Gray-code transport of
-- (24)–(28), (31), (32), which is where the rest of Appendix A.4 goes.

zx-flip : ∀ (a a′ : Fin _) → Succ a a′ → zx a a a′ ≈ zz a a′ • zx a′ a′ a
zx-flip a a′ s = sym
  (trans (cong (axiom (r23 a a′ s)) refl)
  (trans assoc
  (trans (cong refl (cong refl (sym (axiom (r33 a′ a)))))
  (trans (cong refl (axiom (r29 a a′ s))) right-unit))))
