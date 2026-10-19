------------------------------------------------------------------------
-- Presentations of groups
--
-- Separating cosets by an invariant of signed permutations.
--
-- If ψ is unchanged by every letter of the smaller group acting on the
-- left (`ψ-letter`), it is unchanged by every word of it (`ψ-word`);
-- so ψ of label • representative is ψ of the representative, and if
-- the representatives' values are read back to their cosets
-- (`coset-of`), two such words with one signed permutation have one
-- coset (`separate`, CosetExtension's hypothesis).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Maybe.Base using (Maybe ; just)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Perm
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Gamma using (L ; spL ; sp)

module Examples.Groups.CCX+HH.Natural.ThreeWire.Separation
  {T B X C : Set} (ψ : SP → T)
  (fB : B → L) (ψ-letter : ∀ b g → ψ (mul (spL (fB b)) g) ≡ ψ g)
  (fX : X → L) (rep : C → Word X)
  (coset-of : T → Maybe C)
  (coset-of-rep : ∀ c → coset-of (ψ (sp (((λ x → [ fX x ]ʷ) ʷ) (rep c)))) ≡ just c)
  where

private
  E : Word X → Word L
  E = (λ x → [ fX x ]ʷ) ʷ

  F : Word B → Word L
  F = (λ b → [ fB b ]ʷ) ʷ

ψ-word : ∀ l g → ψ (mul (sp (F l)) g) ≡ ψ g
ψ-word [ b ]ʷ  g = ψ-letter b g
ψ-word ε       g = Eq.cong ψ (mul-idˡ g)
ψ-word (u • v) g = Eq.trans (Eq.cong ψ (mul-assoc (sp (F u)) (sp (F v)) g))
  (Eq.trans (ψ-word u (mul (sp (F v)) g)) (ψ-word v g))

private
  just-injective : ∀ {a b : C} → just a ≡ just b → a ≡ b
  just-injective Eq.refl = Eq.refl

separate : ∀ c c′ (l m : Word B) → sp (F l • E (rep c)) ≡ sp (F m • E (rep c′)) → c ≡ c′
separate c c′ l m eq = just-injective (Eq.trans (Eq.sym (coset-of-rep c))
  (Eq.trans (Eq.cong coset-of (Eq.trans (Eq.sym (ψ-word l (sp (E (rep c)))))
    (Eq.trans (Eq.cong ψ eq) (ψ-word m (sp (E (rep c′)))))))
  (coset-of-rep c′)))
