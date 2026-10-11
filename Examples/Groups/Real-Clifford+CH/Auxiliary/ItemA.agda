------------------------------------------------------------------------
-- Presentations of groups
--
-- Item (a) of the Reidemeister–Schreier method
--
-- The first of the two conditions of `Theorem410`: reading a letter of
-- P through f and back through the coset action returns the letter, at
-- the identity coset.  There is one equation per letter shape, and
-- each is exactly one of `DE`'s theorems — the coset action was
-- transcribed so that they would be.
--
--   (−1)(−1)   `DE-ZZ`      a sign pair is the pair through index 1
--   (−1)X      `DE-ZX-all`  a mixed letter sheds its sign onto index 1
--   XX         `DE-XX`      and its two variants, where index 1 is one
--                           of the first exchange's own indices
--
-- The Hadamard shape is the one still open: `DE-HH` covers it only
-- when neither distinguished index occurs among the four, so it is a
-- hypothesis here, and it is the whole of what is left of item (a).
--
-- The action and the traversal are both defined by `with`, and a
-- `with` in a proof will not reduce a *stuck call* to them in the
-- goal.  So each letter's action is computed once, in its own lemma,
-- and `run₂` puts two of those together into a traversal; the proofs
-- then rewrite rather than re-split.  Each is at the Hadamard-free
-- fragment and carried into Figure 8 by `free⇒full-≈`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.ItemA (m : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; _•_ ; _ᵗ ; [_]ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets using (Coset ; ⟨ε⟩ ; ⟨M⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free
  using (_PF,_===_ ; free⇒full-≈)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
  using (GenP ; −1−1 ; −1X ; XX ; HH ; asG)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (act ; o₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410 m
  using (Item-a ; module RS)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m
  using (DE-ZZ ; DE-ZX-all ; DE-XX ; DE-XX-o₁ ; DE-XX-o₂)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m using (gen-zx ; gen-xx)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])

open PB (m PF,_===_) using () renaming (_≈_ to _≈F_ ; trans to transF ; refl' to refl'F)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  Wᴾ : Set
  Wᴾ = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- Two letters through the action

run₂ : ∀ (y y′ : G.Gen N) (w₁ w₂ : Wᴾ) (c₁ c₂ : Coset) →
       act ⟨ε⟩ y ≡ (w₁ , c₁) → act c₁ y′ ≡ (w₂ , c₂) →
       (act ᵗ) ⟨ε⟩ ([ y ]ʷ • [ y′ ]ʷ) ≡ (w₁ • w₂ , c₂)
run₂ y y′ w₁ w₂ c₁ c₂ e₁ e₂ rewrite e₁ | e₂ = Eq.refl

------------------------------------------------------------------------
-- Each letter's action, computed once

act-ε-Z : ∀ (a : Fin N) → act ⟨ε⟩ −1[ a ] ≡ ([ −1−1 {₃₊ m} o₁ a ]ʷ , ⟨M⟩)
act-ε-Z a = Eq.refl

act-M-Z : ∀ (a : Fin N) → act ⟨M⟩ −1[ a ] ≡ ([ −1−1 {₃₊ m} o₁ a ]ʷ , ⟨ε⟩)
act-M-Z a = Eq.refl

act-M-X : ∀ (a b : Fin N) (ne : a ≢ b) →
          act ⟨M⟩ X[ a , b ] ≡ ([ −1X {₃₊ m} o₁ a b ne ]ʷ , ⟨ε⟩)
act-M-X a b ne with a ≟ b
... | yes e = ⊥-elim (ne e)
... | no  _ = Eq.refl

act-ε-X-lo : ∀ (b : Fin N) (ne : o₁ ≢ b) →
             act ⟨ε⟩ X[ o₁ , b ] ≡ ([ −1X {₃₊ m} b o₁ b ne ]ʷ , ⟨M⟩)
act-ε-X-lo b ne with o₁ ≟ b
... | yes e = ⊥-elim (ne e)
... | no  _ with o₁ ≟ o₁
...         | yes _   = Eq.refl
...         | no  bad = ⊥-elim (bad Eq.refl)

act-ε-X-hi : ∀ (a : Fin N) (ne : a ≢ o₁) →
             act ⟨ε⟩ X[ a , o₁ ] ≡ ([ −1X {₃₊ m} a a o₁ ne ]ʷ , ⟨M⟩)
act-ε-X-hi a ne with a ≟ o₁
... | yes e = ⊥-elim (ne e)
... | no  _ with a ≟ o₁
...         | yes e   = ⊥-elim (ne e)
...         | no  _ with o₁ ≟ o₁
...                 | yes _   = Eq.refl
...                 | no  bad = ⊥-elim (bad Eq.refl)

act-ε-X-off : ∀ (a b : Fin N) (ne : a ≢ b) → a ≢ o₁ → b ≢ o₁ →
              act ⟨ε⟩ X[ a , b ] ≡ ([ −1X {₃₊ m} o₁ a b ne ]ʷ , ⟨M⟩)
act-ε-X-off a b ne na nb with a ≟ b
... | yes e = ⊥-elim (ne e)
... | no  _ with a ≟ o₁
...         | yes e = ⊥-elim (na e)
...         | no  _ with b ≟ o₁
...                 | yes e = ⊥-elim (nb e)
...                 | no  _ = Eq.refl

------------------------------------------------------------------------
-- The three Hadamard-free shapes

-- A sign pair: (DE-ZZ).  The traversal is rewritten with `subst`, not
-- `rewrite`: K is disabled, so an equation between two words cannot be
-- matched on.
item-a-zz : ∀ (a b : Fin N) →
            RS._~_ ([ −1−1 {₃₊ m} a b ]ʷ , ⟨ε⟩) ((act ᵗ) ⟨ε⟩ (asG {₃₊ m} (−1−1 {₃₊ m} a b)))
item-a-zz a b =
  Eq.subst (RS._~_ ([ −1−1 {₃₊ m} a b ]ʷ , ⟨ε⟩))
           (Eq.sym (run₂ −1[ a ] −1[ b ] ([ −1−1 {₃₊ m} o₁ a ]ʷ) ([ −1−1 {₃₊ m} o₁ b ]ʷ) ⟨M⟩ ⟨ε⟩
               (act-ε-Z a) (act-M-Z b)))
           (free⇒full-≈ (DE-ZZ a b) , Eq.refl)

-- A mixed letter: (DE-ZX-all).  The distinctness is decided in a
-- helper rather than with a `with`: a `with` would rewrite the goal
-- into the shape of the action's own case split, and the computed
-- actions above would no longer apply to it.
item-a-zx : ∀ (c a b : Fin N) .(ni : a ≢ b) →
            RS._~_ ([ −1X {₃₊ m} c a b ni ]ʷ , ⟨ε⟩)
                   ((act ᵗ) ⟨ε⟩ (asG {₃₊ m} (−1X {₃₊ m} c a b ni)))
item-a-zx c a b ni = go (a ≟ b)
  where
  go : Dec (a ≡ b) →
       RS._~_ ([ −1X {₃₊ m} c a b ni ]ʷ , ⟨ε⟩)
              ((act ᵗ) ⟨ε⟩ (asG {₃₊ m} (−1X {₃₊ m} c a b ni)))
  go (yes e) = ⊥-elim-irr (ni e)
  go (no ne) =
    Eq.subst (RS._~_ ([ −1X {₃₊ m} c a b ni ]ʷ , ⟨ε⟩))
             (Eq.sym (run₂ −1[ c ] X[ a , b ] ([ −1−1 {₃₊ m} o₁ c ]ʷ)
                           ([ −1X {₃₊ m} o₁ a b ne ]ʷ)
                           ⟨M⟩ ⟨ε⟩ (act-ε-Z c) (act-M-X a b ne)))
             (free⇒full-≈ goal , Eq.refl)
    where
    goal : [ −1X {₃₊ m} c a b ni ]ʷ
         ≈F ([ −1−1 {₃₊ m} o₁ c ]ʷ • [ −1X {₃₊ m} o₁ a b ne ]ʷ)
    goal = transF (refl'F (gen-zx c a b ni))
             (transF (DE-ZX-all c a b ne)
                     (refl'F (Eq.cong ([ −1−1 {₃₊ m} o₁ c ]ʷ •_)
                                      (Eq.sym (gen-zx o₁ a b ne)))))

-- A double exchange: (DE-XX), and its two variants.
item-a-xx : ∀ (a b c d : Fin N) .(ni : a ≢ b) .(ni′ : c ≢ d) →
            RS._~_ ([ XX {₃₊ m} a b c d ni ni′ ]ʷ , ⟨ε⟩)
                   ((act ᵗ) ⟨ε⟩ (asG {₃₊ m} (XX {₃₊ m} a b c d ni ni′)))
item-a-xx a b c d ni ni′ = go (a ≟ b) (c ≟ d) (a ≟ o₁) (b ≟ o₁)
  where
  Goal : Set
  Goal = RS._~_ ([ XX {₃₊ m} a b c d ni ni′ ]ʷ , ⟨ε⟩)
                ((act ᵗ) ⟨ε⟩ (asG {₃₊ m} (XX {₃₊ m} a b c d ni ni′)))

  go : Dec (a ≡ b) → Dec (c ≡ d) → Dec (a ≡ o₁) → Dec (b ≡ o₁) → Goal
  go (yes e) _ _ _ = ⊥-elim-irr (ni e)
  go (no _) (yes e) _ _ = ⊥-elim-irr (ni′ e)
  go (no ne) (no ne′) (yes Eq.refl) _ =
    Eq.subst (RS._~_ ([ XX {₃₊ m} a b c d ni ni′ ]ʷ , ⟨ε⟩))
             (Eq.sym (run₂ X[ a , b ] X[ c , d ] ([ −1X {₃₊ m} b o₁ b ne ]ʷ)
                           ([ −1X {₃₊ m} o₁ c d ne′ ]ʷ) ⟨M⟩ ⟨ε⟩
                           (act-ε-X-lo b ne) (act-M-X c d ne′)))
             (free⇒full-≈
                (transF (refl'F (gen-xx a b c d ni ni′))
                   (transF (DE-XX-o₁ b c d ne ne′)
                           (refl'F (Eq.cong₂ _•_ (Eq.sym (gen-zx b o₁ b ne))
                                                 (Eq.sym (gen-zx o₁ c d ne′))))))
              , Eq.refl)
  go (no ne) (no ne′) (no a≢o) (yes Eq.refl) =
    Eq.subst (RS._~_ ([ XX {₃₊ m} a b c d ni ni′ ]ʷ , ⟨ε⟩))
             (Eq.sym (run₂ X[ a , b ] X[ c , d ] ([ −1X {₃₊ m} a a o₁ a≢o ]ʷ)
                           ([ −1X {₃₊ m} o₁ c d ne′ ]ʷ) ⟨M⟩ ⟨ε⟩
                           (act-ε-X-hi a a≢o) (act-M-X c d ne′)))
             (free⇒full-≈
                (transF (refl'F (gen-xx a b c d ni ni′))
                   (transF (DE-XX-o₂ a c d a≢o ne′)
                           (refl'F (Eq.cong₂ _•_ (Eq.sym (gen-zx a a o₁ a≢o))
                                                 (Eq.sym (gen-zx o₁ c d ne′))))))
              , Eq.refl)
  go (no ne) (no ne′) (no a≢o) (no b≢o) =
    Eq.subst (RS._~_ ([ XX {₃₊ m} a b c d ni ni′ ]ʷ , ⟨ε⟩))
             (Eq.sym (run₂ X[ a , b ] X[ c , d ] ([ −1X {₃₊ m} o₁ a b ne ]ʷ)
                           ([ −1X {₃₊ m} o₁ c d ne′ ]ʷ) ⟨M⟩ ⟨ε⟩
                           (act-ε-X-off a b ne a≢o b≢o) (act-M-X c d ne′)))
             (free⇒full-≈
                (transF (refl'F (gen-xx a b c d ni ni′))
                   (transF (DE-XX a b c d ne ne′ (λ e → a≢o (Eq.sym e))
                                                 (λ e → b≢o (Eq.sym e)))
                           (refl'F (Eq.cong₂ _•_ (Eq.sym (gen-zx o₁ a b ne))
                                                 (Eq.sym (gen-zx o₁ c d ne′))))))
              , Eq.refl)

------------------------------------------------------------------------
-- Item (a), modulo the Hadamard shape

Item-a-HH : Set
Item-a-HH = ∀ (a b c d : Fin N) .(ni : a ≢ b) .(ni′ : c ≢ d) →
            RS._~_ ([ HH {₃₊ m} a b c d ni ni′ ]ʷ , ⟨ε⟩)
                   ((act ᵗ) ⟨ε⟩ (asG {₃₊ m} (HH {₃₊ m} a b c d ni ni′)))

module _ (item-a-hh : Item-a-HH) where

  item-a : Item-a
  item-a (−1−1 a b)         = item-a-zz a b
  item-a (−1X c a b ni)     = item-a-zx c a b ni
  item-a (XX a b c d ni n′) = item-a-xx a b c d ni n′
  item-a (HH a b c d ni n′) = item-a-hh a b c d ni n′
