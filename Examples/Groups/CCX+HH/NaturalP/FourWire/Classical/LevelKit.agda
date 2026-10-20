------------------------------------------------------------------------
-- Presentations of groups
--
-- One level of the four-wire classical tower, from its tables.
--
-- A level has letters Fin nX and the level below letters Fin nB, both
-- read as letters L (ιX, ιB); the level below is complete (`lower`).
-- `normE` is the equation between two lists over the level below with
-- one permutation, by that completeness: the "norm" steps of the
-- generated derivations.  `Table` takes the literal coset table — the
-- representatives, the label and next coset of each entry, and the
-- derived equation of each entry, checked against them by one boolean
-- — an invariant separating the cosets with its lookup table, and
-- concludes that the level is complete (CosetExtension).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Pure

module Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.LevelKit
  {nX nB : ℕ} (ιX : Fin nX → L) (ιB : Fin nB → L)
  (lower : ∀ (l m : Word (Fin nB)) →
           sp (((λ b → [ ιB b ]ʷ) ʷ) l) ≡ sp (((λ b → [ ιB b ]ʷ) ʷ) m) →
           ((λ b → [ ιB b ]ʷ) ʷ) l ≈ ((λ b → [ ιB b ]ʷ) ʷ) m)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
import Data.List.Properties as LP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; lookup)
import Presentation.Base as PB
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound ; eqF ; eqF-sound)
open import Presentation.Rewrite _Γ_ eqL eqL-sound using () renaming (eqL to eqList ; eqL-sound to eqList-sound)
import Presentation.CosetExtension as CE
import Examples.Groups.CCX+HH.NaturalP.FourWire.Classical.Separation as Sep

open PB _Γ_ using (refl ; sym ; trans ; cong ; right-unit)

E : Word (Fin nX) → Word L
E = (λ x → [ ιX x ]ʷ) ʷ

F : Word (Fin nB) → Word L
F = (λ b → [ ιB b ]ʷ) ʷ

private
  ≡→≈ : ∀ {u v : Word L} → u ≡ v → u ≈ v
  ≡→≈ Eq.refl = refl

------------------------------------------------------------------------
-- Norm steps

normE : (u v : List (Fin nB)) → sp ⟪ map ιB u ⟫ ≡ sp ⟪ map ιB v ⟫ → Eqn
normE u v h = eqn (map ιB u) (map ιB v)
  (trans (≡→≈ (⟪map⟫ ιB u)) (trans (lower (word-of-list u) (word-of-list v) h′)
    (≡→≈ (Eq.sym (⟪map⟫ ιB v)))))
  where
  h′ : sp (F (word-of-list u)) ≡ sp (F (word-of-list v))
  h′ = Eq.subst₂ (λ a b → sp a ≡ sp b) (⟪map⟫ ιB u) (⟪map⟫ ιB v) h

------------------------------------------------------------------------
-- A table

private
  maybeEq : ∀ {n} → Maybe (Fin n) → Fin n → Bool
  maybeEq (just a) b = eqF a b
  maybeEq nothing  b = false

  maybeEq-sound : ∀ {n} (m : Maybe (Fin n)) b → maybeEq m b ≡ true → m ≡ just b
  maybeEq-sound (just a) b h = Eq.cong just (eqF-sound a b h)

  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = Eq.refl

  ∧-r : ∀ a {b} → a ∧ b ≡ true → b ≡ true
  ∧-r true h = h

find : {T C : Set} → (T → T → Bool) → List (T × C) → T → Maybe C
find eqT []             t = nothing
find eqT ((u , c) ∷ cs) t with eqT u t
... | true  = just c
... | false = find eqT cs t

module Table
  {ck : ℕ}
  (repL : Vec (List (Fin nX)) ck)
  (tab : Vec (Vec (List (Fin nB) × Fin ck) nX) ck)
  (factT : Vec (Vec Eqn nX) ck)
  {T : Set} (ψ : P → T) (ψ-letter : ∀ b g → ψ (mul (spL (ιB b)) g) ≡ ψ g)
  (eqT : T → T → Bool) (cosets : List (T × Fin ck))
  (I : Fin ck) (rep-I : lookup repL I ≡ [])
  where

  rep : Fin ck → Word (Fin nX)
  rep c = word-of-list (lookup repL c)

  h : Fin ck → Fin nX → Word (Fin nB) × Fin ck
  h c x = word-of-list (proj₁ (lookup (lookup tab c) x)) , proj₂ (lookup (lookup tab c) x)

  match : Fin ck → Fin nX → Bool
  match c x =
    eqList (lhs e) (map ιX (lookup repL c ++ x ∷ [])) ∧
    eqList (rhs e) (map ιB (proj₁ (lookup (lookup tab c) x)) ++
                    map ιX (lookup repL (proj₂ (lookup (lookup tab c) x))))
    where e = lookup (lookup factT c) x

  coset-of : T → Maybe (Fin ck)
  coset-of = find eqT cosets

  coset-ok : Fin ck → Bool
  coset-ok c = maybeEq (coset-of (ψ (sp (E (rep c))))) c

  module Checked
    (facts-ok : allFin ck (λ c → allFin nX (match c)) ≡ true)
    (cosets-ok : allFin ck coset-ok ≡ true)
    where

    private
      glue : ∀ (r : List (Fin nX)) (x : Fin nX) (l : List (Fin nB)) (r′ : List (Fin nX)) (e : Eqn) →
             lhs e ≡ map ιX (r ++ x ∷ []) → rhs e ≡ map ιB l ++ map ιX r′ →
             E (word-of-list r) • [ ιX x ]ʷ ≈ F (word-of-list l) • E (word-of-list r′)
      glue r x l r′ e el er =
        trans (cong (≡→≈ (Eq.sym (⟪map⟫ ιX r))) (sym right-unit))
        (trans (sym (⟪++⟫ (map ιX r) (ιX x ∷ [])))
        (trans (≡→≈ (Eq.cong ⟪_⟫ (Eq.trans (Eq.sym (LP.map-++ ιX r (x ∷ []))) (Eq.sym el))))
        (trans (prf e)
        (trans (≡→≈ (Eq.cong ⟪_⟫ er))
        (trans (⟪++⟫ (map ιB l) (map ιX r′))
          (cong (≡→≈ (⟪map⟫ ιB l)) (≡→≈ (⟪map⟫ ιX r′))))))))

    fact : ∀ c x → E (rep c) • E [ x ]ʷ ≈ F (proj₁ (h c x)) • E (rep (proj₂ (h c x)))
    fact c x = glue (lookup repL c) x (proj₁ (lookup (lookup tab c) x))
      (lookup repL (proj₂ (lookup (lookup tab c) x))) (lookup (lookup factT c) x)
      (eqList-sound _ _ (∧-l ok)) (eqList-sound _ _ (∧-r (eqList (lhs (lookup (lookup factT c) x)) (map ιX (lookup repL c ++ x ∷ []))) ok))
      where
      ok : match c x ≡ true
      ok = allFin-sound nX (match c) (allFin-sound ck (λ c → allFin nX (match c)) facts-ok c) x

    coset-of-rep : ∀ c → coset-of (ψ (sp (E (rep c)))) ≡ just c
    coset-of-rep c = maybeEq-sound _ c (allFin-sound ck coset-ok cosets-ok c)

    open Sep ψ ιB ψ-letter ιX rep coset-of coset-of-rep using (separate)

    rep-I′ : rep I ≡ ε
    rep-I′ = Eq.cong word-of-list rep-I

    open CE _Γ_ sp mul (λ _ _ → Eq.refl) sound inverse inverse-right
      (λ x → [ ιX x ]ʷ) (λ b → [ ιB b ]ʷ) lower I rep rep-I′ h fact separate
      public using (complete)
