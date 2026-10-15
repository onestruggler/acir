------------------------------------------------------------------------
-- Presentations of groups
--
-- A proof engine for equations between concrete words over any
-- alphabet with an injective code, after Real-Clifford.Engine.
--
-- An equation (Eqn) is a pair of letter lists with a derivation.  A
-- derivation of a new equation is a list of steps `rw i e`, each
-- rewriting the occurrence of lhs e at position i to rhs e; `run`
-- executes them and `derive` turns a successful run into an equation,
-- so that a proof is a list of steps closed by refl.
--
-- Given that every letter is an involution (module Invol), equations
-- transform by rev⁼ (reversing both sides) and rot⁼ k m, which reads
-- l = r as the relator l r⁻¹ = ε, rotates it by k letters and splits
-- it after m.  Lists are in operator order, like words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (WRel)

module Examples.Groups.CCX+HH-3qubit-opus.Engine
  {A : Set} (Γ : WRel A) (code : A → ℕ) (code-inj : ∀ {x y} → code x ≡ code y → x ≡ y) where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; T)
open import Data.Unit.Base using (tt)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (_≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open PB Γ using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)

------------------------------------------------------------------------
-- Letter lists as words

⟪_⟫ : List A → Word A
⟪ [] ⟫     = ε
⟪ x ∷ xs ⟫ = [ x ]ʷ • ⟪ xs ⟫

-- The letters of a word, in order.
flat : Word A → List A
flat [ x ]ʷ   = x ∷ []
flat ε       = []
flat (u • v) = flat u ++ flat v

⟪++⟫ : (xs ys : List A) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
⟪++⟫ []       ys = sym left-unit
⟪++⟫ (x ∷ xs) ys = trans (cong refl (⟪++⟫ xs ys)) (sym assoc)

⟪≡⟫ : {xs ys : List A} → xs ≡ ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
⟪≡⟫ Eq.refl = refl

⟪flat⟫ : (w : Word A) → ⟪ flat w ⟫ ≈ w
⟪flat⟫ [ x ]ʷ   = right-unit
⟪flat⟫ ε       = refl
⟪flat⟫ (u • v) = trans (⟪++⟫ (flat u) (flat v)) (cong (⟪flat⟫ u) (⟪flat⟫ v))

------------------------------------------------------------------------
-- Equality of letters and lists

eqA : A → A → Bool
eqA x y = code x ≡ᵇ code y

eqA-sound : (x y : A) → eqA x y ≡ true → x ≡ y
eqA-sound x y h = code-inj (≡ᵇ⇒≡ (code x) (code y) (Eq.subst T (Eq.sym h) tt))

private
  ∧-l : ∀ {p q} → p ∧ q ≡ true → p ≡ true
  ∧-l {true} _ = Eq.refl
  ∧-r : ∀ {p q} → p ∧ q ≡ true → q ≡ true
  ∧-r {true} h = h

eqL : List A → List A → Bool
eqL []       []       = true
eqL []       (y ∷ ys) = false
eqL (x ∷ xs) []       = false
eqL (x ∷ xs) (y ∷ ys) = eqA x y ∧ eqL xs ys

eqL-sound : (xs ys : List A) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       h = Eq.refl
eqL-sound []       (y ∷ ys) ()
eqL-sound (x ∷ xs) []       ()
eqL-sound (x ∷ xs) (y ∷ ys) h =
  Eq.cong₂ _∷_ (eqA-sound x y (∧-l {eqA x y} {eqL xs ys} h)) (eqL-sound xs ys (∧-r {eqA x y} {eqL xs ys} h))

------------------------------------------------------------------------
-- Equations

record Eqn : Set where
  constructor eqn
  field
    lhs rhs : List A
    prf     : ⟪ lhs ⟫ ≈ ⟪ rhs ⟫

open Eqn public

sym⁼ : Eqn → Eqn
sym⁼ (eqn l r p) = eqn r l (sym p)

-- An equation between words, as letter lists.
of⁼ : {w v : Word A} → w ≈ v → Eqn
of⁼ {w} {v} p = eqn (flat w) (flat v) (trans (⟪flat⟫ w) (trans p (sym (⟪flat⟫ v))))

-- An axiom.
ax⁼ : {w v : Word A} → Γ w v → Eqn
ax⁼ a = of⁼ (axiom a)

-- Back to words: an equation between any two words with its letters.
to≈ : (e : Eqn) {w v : Word A} → flat w ≡ lhs e → flat v ≡ rhs e → w ≈ v
to≈ e {w} {v} Eq.refl Eq.refl = trans (sym (⟪flat⟫ w)) (trans (prf e) (⟪flat⟫ v))

------------------------------------------------------------------------
-- Running a derivation

data Step : Set where
  rw : ℕ → Eqn → Step

rewrite-at : ℕ → Eqn → List A → List A
rewrite-at i e xs = take i xs ++ (rhs e ++ drop (length (lhs e)) (drop i xs))

matches-at : ℕ → Eqn → List A → Bool
matches-at i e xs = eqL (take (length (lhs e)) (drop i xs)) (lhs e)

run : List Step → List A → Maybe (List A)
run []            xs = just xs
run (rw i e ∷ ss) xs = if matches-at i e xs then run ss (rewrite-at i e xs) else nothing

rw-sound : (i : ℕ) (e : Eqn) (xs : List A) → matches-at i e xs ≡ true → ⟪ xs ⟫ ≈ ⟪ rewrite-at i e xs ⟫
rw-sound i e xs h = begin
  ⟪ xs ⟫                                          ≈⟨ ⟪≡⟫ (Eq.sym (take++drop≡id i xs)) ⟩
  ⟪ take i xs ++ drop i xs ⟫                      ≈⟨ ⟪++⟫ (take i xs) (drop i xs) ⟩
  ⟪ take i xs ⟫ • ⟪ drop i xs ⟫                   ≈⟨ cong refl (⟪≡⟫ (Eq.sym (take++drop≡id m (drop i xs)))) ⟩
  ⟪ take i xs ⟫ • ⟪ take m (drop i xs) ++ rest ⟫  ≈⟨ cong refl (⟪++⟫ (take m (drop i xs)) rest) ⟩
  ⟪ take i xs ⟫ • (⟪ take m (drop i xs) ⟫ • ⟪ rest ⟫)
                                                  ≈⟨ cong refl (cong (⟪≡⟫ (eqL-sound _ _ h)) refl) ⟩
  ⟪ take i xs ⟫ • (⟪ lhs e ⟫ • ⟪ rest ⟫)          ≈⟨ cong refl (cong (prf e) refl) ⟩
  ⟪ take i xs ⟫ • (⟪ rhs e ⟫ • ⟪ rest ⟫)          ≈⟨ cong refl (sym (⟪++⟫ (rhs e) rest)) ⟩
  ⟪ take i xs ⟫ • ⟪ rhs e ++ rest ⟫               ≈⟨ sym (⟪++⟫ (take i xs) (rhs e ++ rest)) ⟩
  ⟪ rewrite-at i e xs ⟫                           ∎
  where
  open SR (PP.word-setoid Γ)
  m = length (lhs e)
  rest = drop m (drop i xs)

run-sound : (ss : List Step) (xs ys : List A) → run ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
run-sound []            xs ys Eq.refl = refl
run-sound (rw i e ∷ ss) xs ys h with matches-at i e xs in c
run-sound (rw i e ∷ ss) xs ys h  | true  = trans (rw-sound i e xs c) (run-sound ss (rewrite-at i e xs) ys h)
run-sound (rw i e ∷ ss) xs ys () | false

-- A derivation: an equation from the steps that turn l into r.
derive : (l r : List A) (ss : List Step) → run ss l ≡ just r → Eqn
derive l r ss h = eqn l r (run-sound ss l r h)

------------------------------------------------------------------------
-- When every letter is an involution

rev : {B : Set} → List B → List B
rev []       = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

module Invol (invol : (x : A) → [ x ]ʷ • [ x ]ʷ ≈ ε) where

  rev-inv : (xs : List A) → ⟪ rev xs ⟫ • ⟪ xs ⟫ ≈ ε
  rev-inv []       = left-unit
  rev-inv (x ∷ xs) = begin
    ⟪ rev xs ++ (x ∷ []) ⟫ • ([ x ]ʷ • ⟪ xs ⟫)        ≈⟨ cong (⟪++⟫ (rev xs) (x ∷ [])) refl ⟩
    (⟪ rev xs ⟫ • ([ x ]ʷ • ε)) • ([ x ]ʷ • ⟪ xs ⟫)   ≈⟨ cong (cong refl right-unit) refl ⟩
    (⟪ rev xs ⟫ • [ x ]ʷ) • ([ x ]ʷ • ⟪ xs ⟫)         ≈⟨ assoc ⟩
    ⟪ rev xs ⟫ • ([ x ]ʷ • ([ x ]ʷ • ⟪ xs ⟫))         ≈⟨ cong refl (sym assoc) ⟩
    ⟪ rev xs ⟫ • (([ x ]ʷ • [ x ]ʷ) • ⟪ xs ⟫)         ≈⟨ cong refl (trans (cong (invol x) refl) left-unit) ⟩
    ⟪ rev xs ⟫ • ⟪ xs ⟫                               ≈⟨ rev-inv xs ⟩
    ε                                                 ∎
    where open SR (PP.word-setoid Γ)

  inv-rev : (xs : List A) → ⟪ xs ⟫ • ⟪ rev xs ⟫ ≈ ε
  inv-rev []       = left-unit
  inv-rev (x ∷ xs) = begin
    ([ x ]ʷ • ⟪ xs ⟫) • ⟪ rev xs ++ (x ∷ []) ⟫        ≈⟨ cong refl (⟪++⟫ (rev xs) (x ∷ [])) ⟩
    ([ x ]ʷ • ⟪ xs ⟫) • (⟪ rev xs ⟫ • ([ x ]ʷ • ε))   ≈⟨ cong refl (cong refl right-unit) ⟩
    ([ x ]ʷ • ⟪ xs ⟫) • (⟪ rev xs ⟫ • [ x ]ʷ)         ≈⟨ assoc ⟩
    [ x ]ʷ • (⟪ xs ⟫ • (⟪ rev xs ⟫ • [ x ]ʷ))         ≈⟨ cong refl (sym assoc) ⟩
    [ x ]ʷ • ((⟪ xs ⟫ • ⟪ rev xs ⟫) • [ x ]ʷ)         ≈⟨ cong refl (trans (cong (inv-rev xs) refl) left-unit) ⟩
    [ x ]ʷ • [ x ]ʷ                                   ≈⟨ invol x ⟩
    ε                                                 ∎
    where open SR (PP.word-setoid Γ)

  -- If u • v ≈ ε then u ≈ v⁻¹, the reversal of v.
  inverse-of : (xs ys : List A) → ⟪ xs ⟫ • ⟪ ys ⟫ ≈ ε → ⟪ xs ⟫ ≈ ⟪ rev ys ⟫
  inverse-of xs ys e = begin
    ⟪ xs ⟫                              ≈⟨ sym right-unit ⟩
    ⟪ xs ⟫ • ε                          ≈⟨ cong refl (sym (inv-rev ys)) ⟩
    ⟪ xs ⟫ • (⟪ ys ⟫ • ⟪ rev ys ⟫)      ≈⟨ sym assoc ⟩
    (⟪ xs ⟫ • ⟪ ys ⟫) • ⟪ rev ys ⟫      ≈⟨ trans (cong e refl) left-unit ⟩
    ⟪ rev ys ⟫                          ∎
    where open SR (PP.word-setoid Γ)

  rotate-relator : (xs ys : List A) → ⟪ xs ⟫ • ⟪ ys ⟫ ≈ ε → ⟪ ys ⟫ • ⟪ xs ⟫ ≈ ε
  rotate-relator xs ys e = trans (cong refl (inverse-of xs ys e)) (inv-rev ys)

  rev-cong : (xs ys : List A) → ⟪ xs ⟫ ≈ ⟪ ys ⟫ → ⟪ rev xs ⟫ ≈ ⟪ rev ys ⟫
  rev-cong xs ys e = inverse-of (rev xs) ys (trans (cong refl (sym e)) (rev-inv xs))

  rev⁼ : Eqn → Eqn
  rev⁼ (eqn l r p) = eqn (rev l) (rev r) (rev-cong l r p)

  -- The relator l r⁻¹ = ε, rotated by k and split after m.
  relator : Eqn → List A
  relator e = lhs e ++ rev (rhs e)

  rotated : ℕ → Eqn → List A
  rotated k e = drop k (relator e) ++ take k (relator e)

  relator-ε : (e : Eqn) → ⟪ relator e ⟫ ≈ ε
  relator-ε (eqn l r p) = trans (⟪++⟫ l (rev r)) (trans (cong p refl) (inv-rev r))

  split-ε : (k : ℕ) (xs : List A) → ⟪ xs ⟫ ≈ ε → ⟪ take k xs ⟫ • ⟪ drop k xs ⟫ ≈ ε
  split-ε k xs e = trans (sym (⟪++⟫ (take k xs) (drop k xs))) (trans (⟪≡⟫ (take++drop≡id k xs)) e)

  rotated-ε : (k : ℕ) (e : Eqn) → ⟪ rotated k e ⟫ ≈ ε
  rotated-ε k e = trans (⟪++⟫ (drop k (relator e)) (take k (relator e)))
    (rotate-relator (take k (relator e)) (drop k (relator e)) (split-ε k (relator e) (relator-ε e)))

  rot⁼ : ℕ → ℕ → Eqn → Eqn
  rot⁼ k m e = eqn (take m (rotated k e)) (rev (drop m (rotated k e)))
    (inverse-of (take m (rotated k e)) (drop m (rotated k e)) (split-ε m (rotated k e) (rotated-ε k e)))
