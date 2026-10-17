------------------------------------------------------------------------
-- Presentations of groups
--
-- The λ-calculus on words, at every width
--
-- Five.Calc at a domain of 4 + n wires: from (F4) and (F5) for
-- generators (Stable.Calc, Stable.Mixed), the same for words (`F4ʷ`,
-- `F5ʷ`); λ⁰ of a word is λ¹ of it between two X on the control
-- (`λ⁰-X`), so λ⁰ carries derivations as λ¹ does (`transport⁰`, from the
-- transport, a module parameter); hence a domain word commuting with G
-- passes λ⁰ G (`pass⁰`), and so does every λ¹-image (`pass¹`) — what the
-- gadgets of the affine decoding, λ⁰ of the gadgets one width down,
-- need.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)

module Examples.Groups.Clifford+CS.Stable.CalcW
  (n : ℕ) (f4 : F4ᵗ n) (f5 : F5ᵗ n)
  (tr : ∀ {u v : Circuit (₄₊ n)} → (₄₊ n) ⊢ᵧ u ≈ v → (suc (₄₊ n)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ ; λ⁰ ; λ⁰ʷ ; Xᵗ)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Mixed using (Xᵗ²)

private
  W D : ℕ
  W = suc (₄₊ n)
  D = ₄₊ n

  x : Circuit W
  x = Xᵗ (₄₊ n)

open Tools (W YVRel,_===_)

------------------------------------------------------------------------
-- Commutation extends from letters to words

private
  left : ∀ (g : Gen D) (v : Circuit D) → λ⁰ g • λ¹ʷ v ≈ λ¹ʷ v • λ⁰ g
  left g [ h ]ʷ  = f4 g h
  left g ε       = trans right-unit (sym left-unit)
  left g (u • v) = begin
    λ⁰ g • (λ¹ʷ u • λ¹ʷ v)            ≈⟨ sym assoc ⟩
    (λ⁰ g • λ¹ʷ u) • λ¹ʷ v            ≈⟨ front _ (left g u) ⟩
    (λ¹ʷ u • λ⁰ g) • λ¹ʷ v            ≈⟨ assoc ⟩
    λ¹ʷ u • (λ⁰ g • λ¹ʷ v)            ≈⟨ back _ (left g v) ⟩
    λ¹ʷ u • (λ¹ʷ v • λ⁰ g)            ≈⟨ sym assoc ⟩
    (λ¹ʷ u • λ¹ʷ v) • λ⁰ g            ∎

-- (F4) for words.
F4ʷ : ∀ (u v : Circuit D) → λ⁰ʷ u • λ¹ʷ v ≈ λ¹ʷ v • λ⁰ʷ u
F4ʷ [ g ]ʷ  v = left g v
F4ʷ ε       v = trans left-unit (sym right-unit)
F4ʷ (u • w) v = begin
  (λ⁰ʷ u • λ⁰ʷ w) • λ¹ʷ v           ≈⟨ assoc ⟩
  λ⁰ʷ u • (λ⁰ʷ w • λ¹ʷ v)           ≈⟨ back _ (F4ʷ w v) ⟩
  λ⁰ʷ u • (λ¹ʷ v • λ⁰ʷ w)           ≈⟨ sym assoc ⟩
  (λ⁰ʷ u • λ¹ʷ v) • λ⁰ʷ w           ≈⟨ front _ (F4ʷ u v) ⟩
  (λ¹ʷ v • λ⁰ʷ u) • λ⁰ʷ w           ≈⟨ assoc ⟩
  λ¹ʷ v • (λ⁰ʷ u • λ⁰ʷ w)           ∎

-- (F5) for words: a domain word is its white and black halves.
F5ʷ : ∀ (w : Circuit D) → top w ≈ λ⁰ʷ w • λ¹ʷ w
F5ʷ [ g ]ʷ  = f5 g
F5ʷ ε       = sym left-unit
F5ʷ (u • v) = begin
  top u • top v                             ≈⟨ cong (F5ʷ u) (F5ʷ v) ⟩
  (λ⁰ʷ u • λ¹ʷ u) • (λ⁰ʷ v • λ¹ʷ v)         ≈⟨ assoc ⟩
  λ⁰ʷ u • (λ¹ʷ u • (λ⁰ʷ v • λ¹ʷ v))         ≈⟨ back _ (sym assoc) ⟩
  λ⁰ʷ u • ((λ¹ʷ u • λ⁰ʷ v) • λ¹ʷ v)         ≈⟨ back _ (front _ (sym (F4ʷ v u))) ⟩
  λ⁰ʷ u • ((λ⁰ʷ v • λ¹ʷ u) • λ¹ʷ v)         ≈⟨ back _ assoc ⟩
  λ⁰ʷ u • (λ⁰ʷ v • (λ¹ʷ u • λ¹ʷ v))         ≈⟨ sym assoc ⟩
  (λ⁰ʷ u • λ⁰ʷ v) • (λ¹ʷ u • λ¹ʷ v)         ∎

------------------------------------------------------------------------
-- λ⁰ is λ¹ between two X on the control

private
  xx : x • x ≈ ε
  xx = embed (Xᵗ² (₄₊ n))

λ⁰-X : ∀ (w : Circuit D) → λ⁰ʷ w ≈ x • λ¹ʷ w • x
λ⁰-X [ g ]ʷ  = refl
λ⁰-X ε       = sym (trans (back _ left-unit) xx)
λ⁰-X (u • v) = begin
  λ⁰ʷ u • λ⁰ʷ v                                    ≈⟨ cong (λ⁰-X u) (λ⁰-X v) ⟩
  (x • λ¹ʷ u • x) • (x • λ¹ʷ v • x)                ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  x • λ¹ʷ u • (x • x) • λ¹ʷ v • x                  ≈⟨ back _ (back _ (front _ xx)) ⟩
  x • λ¹ʷ u • ε • λ¹ʷ v • x                        ≈⟨ back _ (back _ left-unit) ⟩
  x • λ¹ʷ u • λ¹ʷ v • x                            ≈⟨ back _ (sym assoc) ⟩
  x • (λ¹ʷ u • λ¹ʷ v) • x                          ∎

transport⁰ : ∀ {u v : Circuit D} → D ⊢ᵧ u ≈ v → λ⁰ʷ u ≈ λ⁰ʷ v
transport⁰ {u} {v} e = trans (λ⁰-X u) (trans (back _ (front _ (tr e))) (sym (λ⁰-X v)))

------------------------------------------------------------------------
-- Passing λ⁰ of a circuit one width down

-- A domain word commuting with G passes λ⁰ G.
pass⁰ : (g G : Circuit D) → D ⊢ᵧ g • G ≈ G • g → top g • λ⁰ʷ G ≈ λ⁰ʷ G • top g
pass⁰ g G e = begin
  top g • λ⁰ʷ G                             ≈⟨ front _ (F5ʷ g) ⟩
  (λ⁰ʷ g • λ¹ʷ g) • λ⁰ʷ G                   ≈⟨ assoc ⟩
  λ⁰ʷ g • (λ¹ʷ g • λ⁰ʷ G)                   ≈⟨ back _ (sym (F4ʷ G g)) ⟩
  λ⁰ʷ g • (λ⁰ʷ G • λ¹ʷ g)                   ≈⟨ sym assoc ⟩
  (λ⁰ʷ g • λ⁰ʷ G) • λ¹ʷ g                   ≈⟨ front _ (transport⁰ e) ⟩
  (λ⁰ʷ G • λ⁰ʷ g) • λ¹ʷ g                   ≈⟨ assoc ⟩
  λ⁰ʷ G • (λ⁰ʷ g • λ¹ʷ g)                   ≈⟨ back _ (sym (F5ʷ g)) ⟩
  λ⁰ʷ G • top g                             ∎

-- Every λ¹-image passes λ⁰ G.
pass¹ : (h G : Circuit D) → λ¹ʷ h • λ⁰ʷ G ≈ λ⁰ʷ G • λ¹ʷ h
pass¹ h G = sym (F4ʷ G h)

------------------------------------------------------------------------
-- Conjugating λ⁰ by a domain circuit (Five.Conj)

conj⁰ : (a a′ G : Circuit D) → D ⊢ᵧ a • a′ ≈ ε → top a • λ⁰ʷ G • top a′ ≈ λ⁰ʷ (a • G • a′)
conj⁰ a a′ G e = begin
  top a • λ⁰ʷ G • top a′
    ≈⟨ cong (F5ʷ a) (back (λ⁰ʷ G) (F5ʷ a′)) ⟩
  (λ⁰ʷ a • λ¹ʷ a) • λ⁰ʷ G • (λ⁰ʷ a′ • λ¹ʷ a′)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • (□ • □)) Eq.refl ⟩
  λ⁰ʷ a • (λ¹ʷ a • λ⁰ʷ G) • (λ⁰ʷ a′ • λ¹ʷ a′)
    ≈⟨ back (λ⁰ʷ a) (front _ (sym (F4ʷ G a))) ⟩
  λ⁰ʷ a • (λ⁰ʷ G • λ¹ʷ a) • (λ⁰ʷ a′ • λ¹ʷ a′)
    ≈⟨ back (λ⁰ʷ a) (by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl) ⟩
  λ⁰ʷ a • λ⁰ʷ G • (λ¹ʷ a • λ⁰ʷ a′) • λ¹ʷ a′
    ≈⟨ back (λ⁰ʷ a) (back (λ⁰ʷ G) (front _ (sym (F4ʷ a′ a)))) ⟩
  λ⁰ʷ a • λ⁰ʷ G • (λ⁰ʷ a′ • λ¹ʷ a) • λ¹ʷ a′
    ≈⟨ back (λ⁰ʷ a) (back (λ⁰ʷ G) assoc) ⟩
  λ⁰ʷ a • λ⁰ʷ G • λ⁰ʷ a′ • (λ¹ʷ a • λ¹ʷ a′)
    ≈⟨ back (λ⁰ʷ a) (back (λ⁰ʷ G) (back (λ⁰ʷ a′) (tr e))) ⟩
  λ⁰ʷ a • λ⁰ʷ G • λ⁰ʷ a′ • ε
    ≈⟨ back (λ⁰ʷ a) (back (λ⁰ʷ G) right-unit) ⟩
  λ⁰ʷ a • λ⁰ʷ G • λ⁰ʷ a′ ∎
