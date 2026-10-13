------------------------------------------------------------------------
-- Presentations of groups
--
-- A commutation, evaluated on its two factors
--
-- `evaluated Eq.refl : Evaluated (A • B) (B • A)` reads both sides as
-- words, so the gates of A and of B are each applied twice, once in
-- each order.  `comm-evaluated` reads each factor once (⟦_⟧R) and
-- compares the two products of the stored matrices: half the row
-- operations, for two dense products — a gain as soon as the factors
-- are longer than a few gates, which the evaluations of GeneralN's
-- Base modules always are.
--
-- `comm-all` goes further for a family of commutations sharing a
-- factor: the factors are arguments of the one boolean that decides
-- the whole family, so each is read once for all of it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.CommEval where

open import Data.Bool using (Bool ; true ; false ; _∧_)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using () renaming (+-comm to +ℕ-comm)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧M ; len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R ; ⟦⟧R≡⟦⟧M)
open import Examples.Groups.Real-Clifford+CH.Soundness.Relators using (≡-same)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)

private
  variable
    k : ℕ

-- Two stored matrices commute.
Comm : Mat k → Mat k → Bool
Comm A B = eqM (mulM A B) (mulM B A)

-- A commutation of words, from its factors' matrices.
comm-evaluated : (A B : Circuit k) → Comm ⟦ A ⟧R ⟦ B ⟧R ≡ true →
                 Evaluated (A • B) (B • A)
comm-evaluated A B h = evaluated (≡-same (A • B) (B • A) e)
  where
  p : mulM ⟦ A ⟧M ⟦ B ⟧M ≡ mulM ⟦ B ⟧M ⟦ A ⟧M
  p = Eq.subst₂ (λ X Y → mulM X Y ≡ mulM Y X) (⟦⟧R≡⟦⟧M A) (⟦⟧R≡⟦⟧M B)
                (eqM-sound (mulM ⟦ A ⟧R ⟦ B ⟧R) (mulM ⟦ B ⟧R ⟦ A ⟧R) h)

  e : scaleM (√2^ len (B • A)) ⟦ A • B ⟧M ≡ scaleM (√2^ len (A • B)) ⟦ B • A ⟧M
  e = Eq.cong₂ (λ n M → scaleM (√2^ n) M) (+ℕ-comm (len B) (len A)) p

------------------------------------------------------------------------
-- A family of commutations, decided by one boolean

-- Every factor of the first list commutes with every one of the second.
-- The matrices are arguments, so the evaluator reads each once for the
-- whole family.
allCommWith : Mat k → List (Mat k) → Bool
allCommWith A []       = true
allCommWith A (B ∷ Bs) = Comm A B ∧ allCommWith A Bs

allComm : List (Mat k) → List (Mat k) → Bool
allComm []       Bs = true
allComm (A ∷ As) Bs = allCommWith A Bs ∧ allComm As Bs

reads : List (Circuit k) → List (Mat k)
reads = map ⟦_⟧R

private
  ∧-l : ∀ {x y : Bool} → x ∧ y ≡ true → x ≡ true
  ∧-l {true}  _ = Eq.refl

  ∧-r : ∀ {x y : Bool} → x ∧ y ≡ true → y ≡ true
  ∧-r {true}  h = h
  ∧-r {false} ()

  with-pair : (A : Mat k) (Bs : List (Circuit k)) → allCommWith A (reads Bs) ≡ true →
              ∀ {B} → B ∈ Bs → Comm A ⟦ B ⟧R ≡ true
  with-pair A (B ∷ Bs) h (here Eq.refl) = ∧-l h
  with-pair A (B ∷ Bs) h (there b)      = with-pair A Bs (∧-r {Comm A ⟦ B ⟧R} h) b

  comm-pair : (As Bs : List (Circuit k)) → allComm (reads As) (reads Bs) ≡ true →
              ∀ {A B} → A ∈ As → B ∈ Bs → Comm ⟦ A ⟧R ⟦ B ⟧R ≡ true
  comm-pair (A ∷ As) Bs h (here Eq.refl) b = with-pair ⟦ A ⟧R Bs (∧-l h) b
  comm-pair (A ∷ As) Bs h (there a)      b =
    comm-pair As Bs (∧-r {allCommWith ⟦ A ⟧R (reads Bs)} h) a b

-- One commutation of the family.
comm-family : (As Bs : List (Circuit k)) → allComm (reads As) (reads Bs) ≡ true →
              ∀ {A B} → A ∈ As → B ∈ Bs → Evaluated (A • B) (B • A)
comm-family As Bs h {A} {B} a b = comm-evaluated A B (comm-pair As Bs h a b)

------------------------------------------------------------------------
-- Families indexed by Booleans

module _ {A : Set} where

  bools : (Bool → A) → List A
  bools f = f true ∷ f false ∷ []

  ∈-bools : (f : Bool → A) (a : Bool) → f a ∈ bools f
  ∈-bools f true  = here Eq.refl
  ∈-bools f false = there (here Eq.refl)

  bools₂ : (Bool → Bool → A) → List A
  bools₂ f = f true true ∷ f true false ∷ f false true ∷ f false false ∷ []

  ∈-bools₂ : (f : Bool → Bool → A) (a b : Bool) → f a b ∈ bools₂ f
  ∈-bools₂ f true  true  = here Eq.refl
  ∈-bools₂ f true  false = there (here Eq.refl)
  ∈-bools₂ f false true  = there (there (here Eq.refl))
  ∈-bools₂ f false false = there (there (there (here Eq.refl)))

  bools₃ : (Bool → Bool → Bool → A) → List A
  bools₃ f = f true true true ∷ f true true false ∷ f true false true ∷ f true false false ∷
             f false true true ∷ f false true false ∷ f false false true ∷ f false false false ∷ []

  ∈-bools₃ : (f : Bool → Bool → Bool → A) (a b c : Bool) → f a b c ∈ bools₃ f
  ∈-bools₃ f true  true  true  = here Eq.refl
  ∈-bools₃ f true  true  false = there (here Eq.refl)
  ∈-bools₃ f true  false true  = there (there (here Eq.refl))
  ∈-bools₃ f true  false false = there (there (there (here Eq.refl)))
  ∈-bools₃ f false true  true  = there (there (there (there (here Eq.refl))))
  ∈-bools₃ f false true  false = there (there (there (there (there (here Eq.refl)))))
  ∈-bools₃ f false false true  = there (there (there (there (there (there (here Eq.refl))))))
  ∈-bools₃ f false false false = there (there (there (there (there (there (there (here Eq.refl)))))))
