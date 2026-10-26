------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows on four wires, by tables of letters
--
-- A four-wire derivation rewrites a run of letters that leaves a wire i
-- idle by one with the same operator: Lemma 5.1 with completeness on
-- three wires (Windows.win).  Every letter of such a run is spelled off
-- wire i, so a table gives, for each letter that is, the three-wire word
-- u with ⟪ g ⟫ ≡ insʷ i u, and a step is `lwin t b xs ys tt tt Eq.refl`:
-- the two `tt` say that the table has every letter, and `Eq.refl` is
-- the one evaluation of the two three-wire words (SemanticSteps.Same).
-- The window libraries (Four/Wins) had spelled out the two words of
-- every window, which Agda elaborated and then compared with the letters
-- of the lemma's statement, two thirds of their checking time; with the
-- tables, each letter's word is elaborated and compared once, in
-- Four.Lits.  This is the literal half of Five.Win for the rules of
-- Syntactics; the module is generic in the letters and in the idle wire.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ) renaming (_+_ to _+ℕ_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Notations using (₁₊)

module Examples.Groups.Clifford+CS.Four.Win
  (i r : ℕ) (Mac : Set) (⟪_⟫ : Mac → Circuit (₁₊ (i +ℕ r))) where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing ; is-just)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics using (_⊢_≈_)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Same)
open import Examples.Groups.Clifford+CS.Windows using (insʷ ; avoidsʷ ; Base ; win)

private
  W : ℕ
  W = ₁₊ (i +ℕ r)

-- A list of letters, read as Four.Chain reads it.
⟪_⟫ʷ : List Mac → Circuit W
⟪ [] ⟫ʷ           = ε
⟪ ℓ ∷ [] ⟫ʷ       = ⟪ ℓ ⟫
⟪ ℓ ∷ (m ∷ ls) ⟫ʷ = ⟪ ℓ ⟫ • ⟪ m ∷ ls ⟫ʷ

------------------------------------------------------------------------
-- Tables

data Ents (F : Mac → Set) : List Mac → Set where
  []  : Ents F []
  _∷_ : ∀ {x xs} → F x → Ents F xs → Ents F (x ∷ xs)

okᵗ : {F : Mac → Set} → ((g : Mac) → Maybe (F g)) → List Mac → Bool
okᵗ t []       = true
okᵗ t (x ∷ xs) = is-just (t x) ∧ okᵗ t xs

get : {F : Mac → Set} (t : (g : Mac) → Maybe (F g)) (xs : List Mac) → T (okᵗ t xs) → Ents F xs
get t []       _ = []
get {F} t (x ∷ xs) p = get₁ (t x) p
  where
  get₁ : (m : Maybe (F x)) → T (is-just m ∧ okᵗ t xs) → Ents F (x ∷ xs)
  get₁ (just e) q = e ∷ get t xs q
  get₁ nothing  ()

private
  ∧-intro : ∀ {a b : Bool} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

------------------------------------------------------------------------
-- Literal windows

record Lit (g : Mac) : Set where
  constructor lit
  field
    u  : Circuit (i +ℕ r)
    av : T (avoidsʷ i u)
    sp : ⟪ g ⟫ ≡ insʷ i u

catL : ∀ {xs} → Ents Lit xs → Circuit (i +ℕ r)
catL []             = ε
catL (e ∷ [])       = Lit.u e
catL (e ∷ (f ∷ es)) = Lit.u e • catL (f ∷ es)

private
  spL : ∀ {xs} (es : Ents Lit xs) → ⟪ xs ⟫ʷ ≡ insʷ i (catL es)
  spL []             = Eq.refl
  spL (e ∷ [])       = Lit.sp e
  spL (e ∷ (f ∷ es)) = Eq.cong₂ _•_ (Lit.sp e) (spL (f ∷ es))

  avL : ∀ {xs} (es : Ents Lit xs) → T (avoidsʷ i (catL es))
  avL []             = tt
  avL (e ∷ [])       = Lit.av e
  avL (e ∷ (f ∷ es)) = ∧-intro (Lit.av e) (avL (f ∷ es))

lwin : (t : (g : Mac) → Maybe (Lit g)) → Base (i +ℕ r) →
       (xs ys : List Mac) (px : T (okᵗ t xs)) (py : T (okᵗ t ys)) →
       Same (catL (get t xs px)) (catL (get t ys py)) →
       W ⊢ ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
lwin t b xs ys px py e =
  Eq.subst₂ (W ⊢_≈_) (Eq.sym (spL ex)) (Eq.sym (spL ey))
    (win i r b (catL ex) (catL ey) (avL ex) (avL ey) e)
  where
  ex = get t xs px
  ey = get t ys py
