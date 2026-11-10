------------------------------------------------------------------------
-- Presentations of groups
--
-- Even words and their symbols, at a variable width
--
-- EvenRS N's rewriting rs ends in the coset of the parity of the word
-- (rs-parity), so an even word, and Symmetric's word for an even
-- permutation, rewrite into symbols with the same permutation
-- (coset-even, coset-sign).  A permutation of j + m states that agrees
-- with liftN j of a conjugate of ρ by r, and is the permutation of an
-- even word, makes ρ even (lift-sign).  Everything here is at variable
-- widths: at a numeral, comparing two spellings of a sign makes Agda
-- evaluate Symmetric's word for the permutation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.XCXCCX-4bit.EvenWord where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-assoc)
open import Data.Fin.Permutation using (Permutation′ ; _⟨$⟩ʳ_ ; _∘ₚ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ᵗ ; _ʷ)
open import Examples.Groups.Alternating.Semantics using (Alt)

import Examples.Groups.Symmetric.Interpretation as SymI
import Examples.Groups.Symmetric.Surjectivity as SSurj
import Examples.Groups.Symmetric.CoxeterFrames as CF
open import Examples.Groups.Alternating.Parity using (sign ; sign-of ; parity)
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox
import Examples.Groups.XCXCCX-4bit.EvenRS as ERS
open import Examples.Groups.XCXCCX-4bit.NFLib using (sign-by-liftN ; sign-sandwich)

module Coset (N : ℕ) where

  open ERS N public using (Sch ; f ; rs)
  open ERS N using (h ; rs-sem)

  -- The coset rs reaches is the parity of the word.
  rs-parity : (c : Bool) (w : Word (Cox.SG N)) → proj₂ (rs c w) ≡ c xor parity w
  rs-parity false [ g ]ʷ = Eq.refl
  rs-parity true  [ g ]ʷ = Eq.refl
  rs-parity false ε      = Eq.refl
  rs-parity true  ε      = Eq.refl
  rs-parity c (u • v) with (h ᵗ) c u | rs-parity c u
  ... | (u′ , c′) | e with (h ᵗ) c′ v | rs-parity c′ v
  ...   | (v′ , c″) | e′ =
    Eq.trans e′ (Eq.trans (Eq.cong (_xor parity v) e) (xor-assoc c (parity u) (parity v)))

  coset-even : (w : Word (Cox.SG N)) → parity w ≡ false → proj₂ (rs false w) ≡ false
  coset-even w pw = Eq.trans (rs-parity false w) (Eq.cong (false xor_) pw)

  -- Symmetric's word for a permutation, read by Symmetric's semantics.
  go-sem : (π : Permutation′ N) → ∀ i → SymI.⟦ proj₁ (SSurj.go N π) ⟧ ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i
  go-sem π = proj₂ (SSurj.go N π)

  -- Symmetric's word for an even permutation.
  coset-sign : (π : Permutation′ N) → sign π ≡ false → proj₂ (rs false (proj₁ (SSurj.go N π))) ≡ false
  coset-sign π s =
    coset-even (proj₁ (SSurj.go N π))
      (Eq.trans (Eq.sym (sign-of {N} (proj₁ (SSurj.go N π)) π (proj₂ (SSurj.go N π)))) s)

  coset-alt : (a : Alt N) → proj₂ (rs false (proj₁ (SSurj.go N (Alt.perm a)))) ≡ false
  coset-alt a = coset-sign (Alt.perm a) (Alt.even a)

  -- The symbols of Symmetric's word for an even permutation, which
  -- denote it.  Clients use these names (and this module's f and rs):
  -- two module applications of EvenRS N spell f differently, and
  -- comparing the spellings evaluates Symmetric's word.
  -- syms is opaque: unfolded, a circuit built from it is reduced
  -- through rs of Symmetric's word whenever two spellings meet.
  opaque
    syms : Alt N → Word Sch
    syms a = proj₁ (rs false (proj₁ (SSurj.go N (Alt.perm a))))

    sym-sem : (a : Alt N) → ∀ i → SymI.⟦ (f ʷ) (syms a) ⟧ ⟨$⟩ʳ i ≡ Alt.perm a ⟨$⟩ʳ i
    sym-sem a i = Eq.trans (rs-sem (proj₁ (SSurj.go N (Alt.perm a))) (coset-alt a) i) (go-sem (Alt.perm a) i)

module Lift (j m : ℕ) where

  -- An even word whose permutation is lifted from a conjugate of ρ.
  lift-sign : (w : Word (Cox.SG (j + m))) → parity w ≡ false → (r ρ : Permutation′ m) →
              (∀ i → SymI.⟦ w ⟧ ⟨$⟩ʳ i ≡ CF.liftN j (r ∘ₚ (ρ ∘ₚ r)) ⟨$⟩ʳ i) → sign ρ ≡ false
  lift-sign w pw r ρ e =
    Eq.trans (Eq.sym (sign-sandwich r ρ))
      (Eq.trans (Eq.sym (sign-by-liftN j (SymI.⟦ w ⟧) (r ∘ₚ (ρ ∘ₚ r)) e))
        (Eq.trans (sign-of {j + m} w (SymI.⟦ w ⟧) (λ _ → Eq.refl)) pw))
