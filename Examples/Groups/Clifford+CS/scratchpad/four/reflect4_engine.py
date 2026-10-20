# Write Four/Reflect.agda, the reflective engine over the macro letters
# (run by reflect4.py).
#   python3 reflect4_engine.py REPO
import re, sys
REPO = sys.argv[1]
F = REPO + '/Examples/Groups/Clifford+CS/Four/'
letters = open(F + 'Letters.agda', encoding='utf-8').read()
macs = re.search(r'data Mac : Set where\n  (.*) : Mac', letters).group(1).split()
gens = []
for k in range(5):
    gens.append('gate₀ I-gate' + ' ↥' * k)
for k in range(4):
    gens += ['gate₁ S-gate' + ' ↥' * k, 'gate₁ K-gate' + ' ↥' * k]
for k in range(3):
    gens.append('gate₂ CS-gate' + ' ↥' * k)


def table(name, ty, items):
    w = max(len(x) for x in items)
    out = [f'code{name} : {ty} → ℕ']
    out += [f'code{name} ({x}){" " * (w - len(x))} = {i}' for i, x in enumerate(items)]
    out += ['', f'table{name} : List ({ty})']
    out += [f'table{name} =']
    out += [f'  ({x}) ∷' for x in items] + ['  []']
    out += ['', f'decode{name} : ℕ → {ty}']
    out += [f'decode{name} n = ix ({items[0]}) table{name} n', '']
    out += [f'decode-code{name} : ∀ x → decode{name} (code{name} x) ≡ x']
    out += [f'decode-code{name} ({x}){" " * (w - len(x))} = Eq.refl' for x in items]
    return '\n'.join(out) + '\n'


body = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire derivations by reflection
--
-- A derivation of Four/D as a list of steps checked by running it, as
-- Clifford+CS.Engine does over generators: `rw k e` replaces the
-- left-hand side of an equation e found at position k by its right-hand
-- side (`rw⁻` the other way round), and `re k n ys` replaces the n
-- letters at k by ys when the two spell the same generators (a
-- re-bracketing, `by-assoc`).  The line is a list of macro letters
-- (Four.Letters), so that a step costs a comparison of a few letters;
-- only a re-bracketing compares generators.  `derive l r ss Eq.refl`
-- checks the whole run in one evaluation, its result compared with r
-- inside it, and gives ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ.  Written by
-- `scratchpad/four/reflect4.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Reflect where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)

open Assoc (_VRel,_===_ 4) using (to-list)

------------------------------------------------------------------------
-- Codes

private
  ix : {A : Set} → A → List A → ℕ → A
  ix d []       _       = d
  ix d (x ∷ xs) zero    = x
  ix d (x ∷ xs) (suc n) = ix d xs n

''' + table('M', 'Mac', macs) + '\n' + table('G', 'Gen 4', gens) + r'''
private
  ≡ᵇ-sound : ∀ x y → (x ≡ᵇ y) ≡ true → x ≡ y
  ≡ᵇ-sound x y h = ≡ᵇ⇒≡ x y (Eq.subst T (Eq.sym h) tt)

eqLM : List Mac → List Mac → Bool
eqLM []       []       = true
eqLM []       (y ∷ ys) = false
eqLM (x ∷ xs) []       = false
eqLM (x ∷ xs) (y ∷ ys) = (codeM x ≡ᵇ codeM y) ∧ eqLM xs ys

eqLM-sound : (xs ys : List Mac) → eqLM xs ys ≡ true → xs ≡ ys
eqLM-sound []       []       h = Eq.refl
eqLM-sound []       (y ∷ ys) ()
eqLM-sound (x ∷ xs) []       ()
eqLM-sound (x ∷ xs) (y ∷ ys) h with codeM x ≡ᵇ codeM y in e
eqLM-sound (x ∷ xs) (y ∷ ys) h  | true  =
  Eq.cong₂ _∷_
    (Eq.trans (Eq.sym (decode-codeM x))
      (Eq.trans (Eq.cong decodeM (≡ᵇ-sound (codeM x) (codeM y) e)) (decode-codeM y)))
    (eqLM-sound xs ys h)
eqLM-sound (x ∷ xs) (y ∷ ys) () | false

eqLG : List (Gen 4) → List (Gen 4) → Bool
eqLG []       []       = true
eqLG []       (y ∷ ys) = false
eqLG (x ∷ xs) []       = false
eqLG (x ∷ xs) (y ∷ ys) = (codeG x ≡ᵇ codeG y) ∧ eqLG xs ys

eqLG-sound : (xs ys : List (Gen 4)) → eqLG xs ys ≡ true → xs ≡ ys
eqLG-sound []       []       h = Eq.refl
eqLG-sound []       (y ∷ ys) ()
eqLG-sound (x ∷ xs) []       ()
eqLG-sound (x ∷ xs) (y ∷ ys) h with codeG x ≡ᵇ codeG y in e
eqLG-sound (x ∷ xs) (y ∷ ys) h  | true  =
  Eq.cong₂ _∷_
    (Eq.trans (Eq.sym (decode-codeG x))
      (Eq.trans (Eq.cong decodeG (≡ᵇ-sound (codeG x) (codeG y) e)) (decode-codeG y)))
    (eqLG-sound xs ys h)
eqLG-sound (x ∷ xs) (y ∷ ys) () | false

------------------------------------------------------------------------
-- Equations and steps

record Eqn : Set where
  constructor eqn
  field
    lhs rhs : List Mac
    prf     : ⟪ lhs ⟫ʷ ≈ ⟪ rhs ⟫ʷ

open Eqn public

data Step : Set where
  rw rw⁻ : ℕ → Eqn → Step
  re     : ℕ → ℕ → List Mac → Step

flat : List Mac → List (Gen 4)
flat ms = to-list ⟪ ms ⟫ʷ

run : List Step → List Mac → Maybe (List Mac)
run []                xs = just xs
run (rw k e ∷ ss)     xs =
  if eqLM (take (length (lhs e)) (drop k xs)) (lhs e)
  then run ss (next k (length (lhs e)) (rhs e) xs) else nothing
run (rw⁻ k e ∷ ss)    xs =
  if eqLM (take (length (rhs e)) (drop k xs)) (rhs e)
  then run ss (next k (length (rhs e)) (lhs e) xs) else nothing
run (re k n ys ∷ ss)  xs =
  if eqLG (flat (take n (drop k xs))) (flat ys)
  then run ss (next k n ys xs) else nothing

check : List Step → List Mac → List Mac → Bool
check ss l r with run ss l
... | just xs = eqLM xs r
... | nothing = false

private
  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
  ≡⇒≈ Eq.refl = refl

run-sound : (ss : List Step) (xs ys : List Mac) → run ss xs ≡ just ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
run-sound []               xs ys Eq.refl = refl
run-sound (rw k e ∷ ss)    xs ys h with eqLM (take (length (lhs e)) (drop k xs)) (lhs e) in c
run-sound (rw k e ∷ ss)    xs ys h  | true  =
  trans (step k (length (lhs e)) xs (rhs e) (trans (≡⇒≈ (eqLM-sound (take (length (lhs e)) (drop k xs)) (lhs e) c)) (prf e)))
        (run-sound ss _ ys h)
run-sound (rw k e ∷ ss)    xs ys () | false
run-sound (rw⁻ k e ∷ ss)   xs ys h with eqLM (take (length (rhs e)) (drop k xs)) (rhs e) in c
run-sound (rw⁻ k e ∷ ss)   xs ys h  | true  =
  trans (step k (length (rhs e)) xs (lhs e) (trans (≡⇒≈ (eqLM-sound (take (length (rhs e)) (drop k xs)) (rhs e) c)) (sym (prf e))))
        (run-sound ss _ ys h)
run-sound (rw⁻ k e ∷ ss)   xs ys () | false
run-sound (re k n zs ∷ ss) xs ys h with eqLG (flat (take n (drop k xs))) (flat zs) in c
run-sound (re k n zs ∷ ss) xs ys h  | true  =
  trans (step k n xs zs (by-assoc {⟪ take n (drop k xs) ⟫ʷ} {⟪ zs ⟫ʷ} (eqLG-sound (flat (take n (drop k xs))) (flat zs) c))) (run-sound ss _ ys h)
run-sound (re k n zs ∷ ss) xs ys () | false

check-sound : (ss : List Step) (l r : List Mac) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
check-sound ss l r h with run ss l in e
check-sound ss l r h  | just xs = trans (run-sound ss l xs e) (≡⇒≈ (eqLM-sound xs r h))
check-sound ss l r () | nothing

-- The equation of a derivation, checked by running it.
derive : (l r : List Mac) (ss : List Step) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
derive l r ss h = check-sound ss l r h
'''
open(F + 'Reflect.agda', 'w', encoding='utf-8', newline='\n').write(body)
print(len(macs), 'letters,', len(gens), 'generators')
