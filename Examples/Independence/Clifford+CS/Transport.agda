------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport of an equation between products of atoms along tokens
--
-- The tokens are involutions, t t ≈ ε, and each passes each atom,
-- t a ≈ (a ^ t) t.  An equation between products of atoms then holds
-- with every atom relabelled by t: conjugate it by t.  Clifford+CS.
-- TwoWire uses this for the two-level relations on four indices: the
-- atoms are the decoded generators, the tokens X on either wire, the
-- swap and a CNOT, which permute the indices, and every instance of a
-- relation is a relabelling of one of them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Word.Base using (ε ; _•_)

open import Examples.Independence.Clifford+CS.Syntactics

module Examples.Independence.Clifford+CS.Transport
  {n : ℕ} {Tok Atom : Set}
  (tok  : Tok → Circuit n)
  (⟦_⟧ᵃ : Atom → Circuit n)
  (_^_  : Atom → Tok → Atom)
  (tt   : ∀ t → n ⊢ tok t • tok t ≈ ε)
  (push : ∀ t a → n ⊢ tok t • ⟦ a ⟧ᵃ ≈ ⟦ a ^ t ⟧ᵃ • tok t)
  where

open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open PB (n VRel,_===_)
open PP (n VRel,_===_) using (word-setoid)
open import Relation.Binary.Reasoning.Setoid word-setoid

------------------------------------------------------------------------
-- Products of atoms and their relabellings

⟦_⟧ˡ : List Atom → Circuit n
⟦ [] ⟧ˡ    = ε
⟦ a ∷ l ⟧ˡ = ⟦ a ⟧ᵃ • ⟦ l ⟧ˡ

_^ˡ_ : List Atom → Tok → List Atom
l ^ˡ t = map (_^ t) l

-- Relabelled by each token in turn.
_^*_ : List Atom → List Tok → List Atom
l ^* []       = l
l ^* (t ∷ ts) = (l ^ˡ t) ^* ts

------------------------------------------------------------------------
-- A token passes a product of atoms, and conjugating by it relabels

push-l : ∀ t l → tok t • ⟦ l ⟧ˡ ≈ ⟦ l ^ˡ t ⟧ˡ • tok t
push-l t []      = trans right-unit (sym left-unit)
push-l t (a ∷ l) = begin
  tok t • (⟦ a ⟧ᵃ • ⟦ l ⟧ˡ)            ≈⟨ sym assoc ⟩
  (tok t • ⟦ a ⟧ᵃ) • ⟦ l ⟧ˡ            ≈⟨ cong (push t a) refl ⟩
  (⟦ a ^ t ⟧ᵃ • tok t) • ⟦ l ⟧ˡ         ≈⟨ assoc ⟩
  ⟦ a ^ t ⟧ᵃ • (tok t • ⟦ l ⟧ˡ)         ≈⟨ cong refl (push-l t l) ⟩
  ⟦ a ^ t ⟧ᵃ • (⟦ l ^ˡ t ⟧ˡ • tok t)    ≈⟨ sym assoc ⟩
  (⟦ a ^ t ⟧ᵃ • ⟦ l ^ˡ t ⟧ˡ) • tok t    ∎

transport : ∀ t {l r} → ⟦ l ⟧ˡ ≈ ⟦ r ⟧ˡ → ⟦ l ^ˡ t ⟧ˡ ≈ ⟦ r ^ˡ t ⟧ˡ
transport t {l} {r} e = begin
  ⟦ l ^ˡ t ⟧ˡ                       ≈⟨ sym right-unit ⟩
  ⟦ l ^ˡ t ⟧ˡ • ε                   ≈⟨ cong refl (sym (tt t)) ⟩
  ⟦ l ^ˡ t ⟧ˡ • (tok t • tok t)     ≈⟨ sym assoc ⟩
  (⟦ l ^ˡ t ⟧ˡ • tok t) • tok t     ≈⟨ cong (sym (push-l t l)) refl ⟩
  (tok t • ⟦ l ⟧ˡ) • tok t          ≈⟨ cong (cong refl e) refl ⟩
  (tok t • ⟦ r ⟧ˡ) • tok t          ≈⟨ cong (push-l t r) refl ⟩
  (⟦ r ^ˡ t ⟧ˡ • tok t) • tok t     ≈⟨ assoc ⟩
  ⟦ r ^ˡ t ⟧ˡ • (tok t • tok t)     ≈⟨ cong refl (tt t) ⟩
  ⟦ r ^ˡ t ⟧ˡ • ε                   ≈⟨ right-unit ⟩
  ⟦ r ^ˡ t ⟧ˡ                       ∎

transport* : ∀ ts {l r} → ⟦ l ⟧ˡ ≈ ⟦ r ⟧ˡ → ⟦ l ^* ts ⟧ˡ ≈ ⟦ r ^* ts ⟧ˡ
transport* []       e = e
transport* (t ∷ ts) e = transport* ts (transport t e)

------------------------------------------------------------------------
-- Standard equations and their instances

record Std : Set where
  constructor std
  field
    lhs rhs : List Atom
    proof   : ⟦ lhs ⟧ˡ ≈ ⟦ rhs ⟧ˡ

-- An equation between words with the letters of a relabelled standard
-- equation.
by : ∀ ts (s : Std) {w v : Circuit n} →
     Assoc.to-list (n VRel,_===_) w ≡ Assoc.to-list (n VRel,_===_) ⟦ Std.lhs s ^* ts ⟧ˡ →
     Assoc.to-list (n VRel,_===_) ⟦ Std.rhs s ^* ts ⟧ˡ ≡ Assoc.to-list (n VRel,_===_) v →
     w ≈ v
by ts s p q =
  trans (PP.by-assoc (n VRel,_===_) p)
        (trans (transport* ts (Std.proof s)) (PP.by-assoc (n VRel,_===_) q))
