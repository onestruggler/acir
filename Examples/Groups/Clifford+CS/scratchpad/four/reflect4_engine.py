# Write TREE/Reflect.agda (TREE Four, Five or FiveV, default Four), the
# reflective engine over the macro letters (run by reflect4.py and
# reflect5.py).
#   python3 reflect4_engine.py REPO [TREE]
import re, sys
REPO = sys.argv[1]
TREE = sys.argv[2] if len(sys.argv) > 2 else 'Four'
W = {'Four': 4, 'Five': 5, 'FiveV': 5}[TREE]
F = REPO + f'/Examples/Groups/Clifford+CS/{TREE}/'
letters = open(F + 'Letters.agda', encoding='utf-8').read()
decl = re.search(r'data Mac : Set where\n((?:  .*\n)+)', letters).group(1)
macs = [x for line in decl.split('\n') if line.strip()
        for x in line.split(':')[0].split()]
gens = []
for k in range(W + 1):
    gens.append('gate₀ I-gate' + ' ↥' * k)
for k in range(W):
    gens += ['gate₁ S-gate' + ' ↥' * k, 'gate₁ K-gate' + ' ↥' * k]
for k in range(W - 1):
    gens.append('gate₂ CS-gate' + ' ↥' * k)
REL = '_VRel,_===_ 4' if TREE == 'Four' else '_XVRel,_===_ 5'
SYN = ('open import Examples.Groups.Clifford+CS.Syntactics' if TREE == 'Four' else
       'open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)\n'
       f'open import Examples.Groups.Clifford+CS.{TREE}.Rules using (_XVRel,_===_)')


# Four's re-bracketings compare their letters' generators through a table
# of each letter's codes (codes_Four.txt, written by codes.sh); Five's
# letters are larger (213,000 codes in all), and a table of them made its
# derivations no faster, the interface every one loads twice the size.
CODES = TREE == 'Four'
if CODES:
    codes_path = REPO + f'/Examples/Groups/Clifford+CS/scratchpad/four/codes_{TREE}.txt'
    codes = [[int(x) for x in line.split()] for line in open(codes_path).read().split('\n')[:len(macs)]]
    assert len(codes) == len(macs), (len(codes), len(macs))


def codes_table():
    w = max(len(x) for x in macs)
    out = ['codesM : Mac → List ℕ']
    out += [f'codesM ({x}){" " * (w - len(x))} = ' + ''.join(f'{c} ∷ ' for c in cs) + '[]'
            for x, cs in zip(macs, codes)]
    out += ['', 'codesM-ok : ∀ x → codesM x ≡ map codeG (flat (x ∷ []))']
    out += [f'codesM-ok ({x}){" " * (w - len(x))} = Eq.refl' for x in macs]
    return '\n'.join(out) + '\n'


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


HOOK_FOUR = r'''------------------------------------------------------------------------
-- Each letter's generators, by their codes

-- Read off the letter's word at every re-bracketing, the generators of
-- a letter cost about a millisecond, most of the time of running a
-- Four/D derivation; here they are a table, checked once.  The codes
-- are scratchpad/four/codes_Four.txt, which codes.sh computes.
@@CODES@@
flatC : List Mac → List ℕ
flatC []       = []
flatC (x ∷ xs) = codesM x ++ flatC xs

eqLN : List ℕ → List ℕ → Bool
eqLN []       []       = true
eqLN []       (y ∷ ys) = false
eqLN (x ∷ xs) []       = false
eqLN (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eqLN xs ys

private
  eqLN-sound : (xs ys : List ℕ) → eqLN xs ys ≡ true → xs ≡ ys
  eqLN-sound []       []       h = Eq.refl
  eqLN-sound []       (y ∷ ys) ()
  eqLN-sound (x ∷ xs) []       ()
  eqLN-sound (x ∷ xs) (y ∷ ys) h with x ≡ᵇ y in e
  eqLN-sound (x ∷ xs) (y ∷ ys) h  | true  = Eq.cong₂ _∷_ (≡ᵇ-sound x y e) (eqLN-sound xs ys h)
  eqLN-sound (x ∷ xs) (y ∷ ys) () | false

  map-++ : (xs ys : List (Gen 4)) → map codeG (xs ++ ys) ≡ map codeG xs ++ map codeG ys
  map-++ []       ys = Eq.refl
  map-++ (x ∷ xs) ys = Eq.cong (codeG x ∷_) (map-++ xs ys)

  ++-[] : (xs : List (Gen 4)) → xs ++ [] ≡ xs
  ++-[] []       = Eq.refl
  ++-[] (x ∷ xs) = Eq.cong (x ∷_) (++-[] xs)

  flat-∷ : (x : Mac) (xs : List Mac) → flat (x ∷ xs) ≡ flat (x ∷ []) ++ flat xs
  flat-∷ x []       = Eq.sym (++-[] (flat (x ∷ [])))
  flat-∷ x (m ∷ ms) = Eq.refl

  flatC-ok : (xs : List Mac) → flatC xs ≡ map codeG (flat xs)
  flatC-ok []       = Eq.refl
  flatC-ok (x ∷ xs) =
    Eq.trans (Eq.cong₂ _++_ (codesM-ok x) (flatC-ok xs))
      (Eq.trans (Eq.sym (map-++ (flat (x ∷ [])) (flat xs))) (Eq.cong (map codeG) (Eq.sym (flat-∷ x xs))))

  map-inj : (xs ys : List (Gen 4)) → map codeG xs ≡ map codeG ys → xs ≡ ys
  map-inj []       []       h = Eq.refl
  map-inj []       (y ∷ ys) ()
  map-inj (x ∷ xs) []       ()
  map-inj (x ∷ xs) (y ∷ ys) h =
    Eq.cong₂ _∷_
      (Eq.trans (Eq.sym (decode-codeG x)) (Eq.trans (Eq.cong decodeG (∷-head h)) (decode-codeG y)))
      (map-inj xs ys (∷-tail h))
    where
    ∷-head : ∀ {a b : ℕ} {as bs} → a ∷ as ≡ b ∷ bs → a ≡ b
    ∷-head Eq.refl = Eq.refl
    ∷-tail : ∀ {a b : ℕ} {as bs} → a ∷ as ≡ b ∷ bs → as ≡ bs
    ∷-tail Eq.refl = Eq.refl

  flat-eq : (xs ys : List Mac) → eqLN (flatC xs) (flatC ys) ≡ true → flat xs ≡ flat ys
  flat-eq xs ys h =
    map-inj (flat xs) (flat ys)
      (Eq.trans (Eq.sym (flatC-ok xs)) (Eq.trans (eqLN-sound (flatC xs) (flatC ys) h) (flatC-ok ys)))

-- Whether two runs of letters spell the same generators.
sameG : List Mac → List Mac → Bool
sameG xs ys = eqLN (flatC xs) (flatC ys)

sameG-ok : (xs ys : List Mac) → sameG xs ys ≡ true → flat xs ≡ flat ys
sameG-ok = flat-eq

'''
HOOK_FIVE = r'''------------------------------------------------------------------------
-- Whether two runs of letters spell the same generators

sameG : List Mac → List Mac → Bool
sameG xs ys = eqLG (flat xs) (flat ys)

sameG-ok : (xs ys : List Mac) → sameG xs ys ≡ true → flat xs ≡ flat ys
sameG-ok xs ys = eqLG-sound (flat xs) (flat ys)

'''
if CODES:
    HOOK_FOUR = HOOK_FOUR.replace('@@CODES@@', codes_table())

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
-- only a re-bracketing compares generators (sameG).  The line is a
-- zipper, so that a step at position k costs its distance from the step
-- before rather than k.  `derive l r ss Eq.refl` checks the whole run
-- in one evaluation, its result compared with r inside it, and gives
-- ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ.  Written by
-- `scratchpad/four/reflect4.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Reflect where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; take ; drop ; map)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; pred ; _∸_ ; _≡ᵇ_ ; _<ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

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

''' + (HOOK_FOUR if CODES else HOOK_FIVE) + r'''------------------------------------------------------------------------
-- The line as a zipper

-- The letters before the focus, last first, and the letters from it on,
-- with the index of the focus.  A step at position k moves the focus
-- there, which costs the distance from the step before: two letters on
-- average in Four/D and Five/D, whose steps are at positions 30 and 47
-- on average, and the line as a list was walked from its start at every
-- step (take, drop and next).  The equation's sides and the parts of
-- the line are handed on as arguments (runZ-rw, runZ-at, runZ-seg), so
-- that Agda's evaluator computes each once.  The engine is that of
-- Qutrit-Clifford.Engine on the ten-completeness branch.
data Zip : Set where
  zp : ℕ → List Mac → List Mac → Zip

revApp : List Mac → List Mac → List Mac
revApp []       ys = ys
revApp (x ∷ xs) ys = revApp xs (x ∷ ys)

plug : Zip → List Mac
plug (zp _ b a) = revApp b a

goL goR : ℕ → Zip → Maybe Zip
goL zero    z                = just z
goL (suc k) (zp c (x ∷ b) a) = goL k (zp (pred c) b (x ∷ a))
goL (suc k) (zp c [] a)      = nothing
goR zero    z                = just z
goR (suc k) (zp c b (x ∷ a)) = goR k (zp (suc c) (x ∷ b) a)
goR (suc k) (zp c b [])      = nothing

seek : ℕ → Zip → Maybe Zip
seek i (zp c b a) = if i <ᵇ c then goL (c ∸ i) (zp c b a) else goR (i ∸ c) (zp c b a)

-- What follows l in a, when l begins a.
strip : List Mac → List Mac → Maybe (List Mac)
strip []      a       = just a
strip (x ∷ l) []      = nothing
strip (x ∷ l) (y ∷ a) = if codeM x ≡ᵇ codeM y then strip l a else nothing

mutual
  runZ : List Step → Zip → Maybe Zip
  runZ []               z = just z
  runZ (rw k e ∷ ss)    z = runZ-rw ss (lhs e) (rhs e) (seek k z)
  runZ (rw⁻ k e ∷ ss)   z = runZ-rw ss (rhs e) (lhs e) (seek k z)
  runZ (re k n ys ∷ ss) z = runZ-re ss n ys (seek k z)

  runZ-rw : List Step → (l r : List Mac) → Maybe Zip → Maybe Zip
  runZ-rw ss l r nothing           = nothing
  runZ-rw ss l r (just (zp c b a)) = runZ-at ss r c b (strip l a)

  runZ-at : List Step → List Mac → ℕ → List Mac → Maybe (List Mac) → Maybe Zip
  runZ-at ss r c b nothing     = nothing
  runZ-at ss r c b (just rest) = runZ ss (zp c b (r ++ rest))

  runZ-re : List Step → ℕ → List Mac → Maybe Zip → Maybe Zip
  runZ-re ss n ys nothing           = nothing
  runZ-re ss n ys (just (zp c b a)) = runZ-seg ss ys c b (take n a) (drop n a)

  runZ-seg : List Step → List Mac → ℕ → (b seg rest : List Mac) → Maybe Zip
  runZ-seg ss ys c b seg rest =
    if sameG seg ys then runZ ss (zp c b (ys ++ rest)) else nothing

okZ : List Mac → Maybe Zip → Bool
okZ r (just z) = eqLM (plug z) r
okZ r nothing  = false

check : List Step → List Mac → List Mac → Bool
check ss l r = okZ r (runZ ss (zp 0 [] l))

private
  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
  ≡⇒≈ Eq.refl = refl

  code-eq : ∀ x y → (codeM x ≡ᵇ codeM y) ≡ true → x ≡ y
  code-eq x y e =
    Eq.trans (Eq.sym (decode-codeM x))
      (Eq.trans (Eq.cong decodeM (≡ᵇ-sound (codeM x) (codeM y) e)) (decode-codeM y))

  lc-∷ : ∀ ℓ ls → ⟪ ℓ ∷ ls ⟫ʷ ≈ ⟪ ℓ ⟫ • ⟪ ls ⟫ʷ
  lc-∷ ℓ []       = sym right-unit
  lc-∷ ℓ (m ∷ ls) = refl

  lc-++ : ∀ xs ys → ⟪ xs ++ ys ⟫ʷ ≈ ⟪ xs ⟫ʷ • ⟪ ys ⟫ʷ
  lc-++ []       ys = sym left-unit
  lc-++ (x ∷ xs) ys =
    trans (lc-∷ x (xs ++ ys))
    (trans (back ⟪ x ⟫ (lc-++ xs ys))
    (trans (sym assoc) (front ⟪ ys ⟫ʷ (sym (lc-∷ x xs)))))

  ++-congˡ : ∀ {x y} s → ⟪ x ⟫ʷ ≈ ⟪ y ⟫ʷ → ⟪ x ++ s ⟫ʷ ≈ ⟪ y ++ s ⟫ʷ
  ++-congˡ {x} {y} s e = trans (lc-++ x s) (trans (front ⟪ s ⟫ʷ e) (sym (lc-++ y s)))

  revApp-cong : (b : List Mac) {x y : List Mac} → ⟪ x ⟫ʷ ≈ ⟪ y ⟫ʷ → ⟪ revApp b x ⟫ʷ ≈ ⟪ revApp b y ⟫ʷ
  revApp-cong []      e = e
  revApp-cong (g ∷ b) {x} {y} e =
    revApp-cong b (trans (lc-∷ g x) (trans (back ⟪ g ⟫ e) (sym (lc-∷ g y))))

  take++drop : (n : ℕ) (xs : List Mac) → take n xs ++ drop n xs ≡ xs
  take++drop zero    xs       = Eq.refl
  take++drop (suc n) []       = Eq.refl
  take++drop (suc n) (x ∷ xs) = Eq.cong (x ∷_) (take++drop n xs)

  -- Moving the focus keeps the line.
  goL-un : (k : ℕ) (z z′ : Zip) → goL k z ≡ just z′ → plug z′ ≡ plug z
  goL-un zero    z                z′ Eq.refl = Eq.refl
  goL-un (suc k) (zp c (x ∷ b) a) z′ h       = goL-un k (zp (pred c) b (x ∷ a)) z′ h
  goL-un (suc k) (zp c [] a)      z′ ()

  goR-un : (k : ℕ) (z z′ : Zip) → goR k z ≡ just z′ → plug z′ ≡ plug z
  goR-un zero    z                z′ Eq.refl = Eq.refl
  goR-un (suc k) (zp c b (x ∷ a)) z′ h       = goR-un k (zp (suc c) (x ∷ b) a) z′ h
  goR-un (suc k) (zp c b [])      z′ ()

  seek-un : (i : ℕ) (z z′ : Zip) → seek i z ≡ just z′ → plug z′ ≡ plug z
  seek-un i (zp c b a) z′ h with i <ᵇ c
  seek-un i (zp c b a) z′ h | true  = goL-un (c ∸ i) (zp c b a) z′ h
  seek-un i (zp c b a) z′ h | false = goR-un (i ∸ c) (zp c b a) z′ h

  strip-sound : (l a rest : List Mac) → strip l a ≡ just rest → a ≡ l ++ rest
  strip-sound []      a       rest Eq.refl = Eq.refl
  strip-sound (x ∷ l) []      rest ()
  strip-sound (x ∷ l) (y ∷ a) rest h with codeM x ≡ᵇ codeM y in e
  strip-sound (x ∷ l) (y ∷ a) rest h  | true  =
    Eq.cong₂ _∷_ (Eq.sym (code-eq x y e)) (strip-sound l a rest h)
  strip-sound (x ∷ l) (y ∷ a) rest () | false

  mutual
    runZ-sound : (ss : List Step) (z z′ : Zip) → runZ ss z ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-sound []               z z′ Eq.refl = refl
    runZ-sound (rw k e ∷ ss)    z z′ h =
      runZ-rw-sound ss (lhs e) (rhs e) (prf e) z (seek k z) (seek-un k z) z′ h
    runZ-sound (rw⁻ k e ∷ ss)   z z′ h =
      runZ-rw-sound ss (rhs e) (lhs e) (sym (prf e)) z (seek k z) (seek-un k z) z′ h
    runZ-sound (re k n ys ∷ ss) z z′ h =
      runZ-re-sound ss n ys z (seek k z) (seek-un k z) z′ h

    runZ-rw-sound : (ss : List Step) (l r : List Mac) → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → (z : Zip) (m : Maybe Zip) →
                    (∀ z₁ → m ≡ just z₁ → plug z₁ ≡ plug z) → (z′ : Zip) →
                    runZ-rw ss l r m ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-rw-sound ss l r p z nothing           u z′ ()
    runZ-rw-sound ss l r p z (just (zp c b a)) u z′ h =
      trans (≡⇒≈ (Eq.sym (u (zp c b a) Eq.refl)))
            (runZ-at-sound ss l r p c b a (strip l a) Eq.refl z′ h)

    runZ-at-sound : (ss : List Step) (l r : List Mac) → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → (c : ℕ) (b a : List Mac) →
                    (m : Maybe (List Mac)) → strip l a ≡ m → (z′ : Zip) →
                    runZ-at ss r c b m ≡ just z′ → ⟪ revApp b a ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-at-sound ss l r p c b a nothing     s z′ ()
    runZ-at-sound ss l r p c b a (just rest) s z′ h =
      trans (revApp-cong b (trans (≡⇒≈ (strip-sound l a rest s)) (++-congˡ {l} {r} rest p)))
            (runZ-sound ss (zp c b (r ++ rest)) z′ h)

    runZ-re-sound : (ss : List Step) (n : ℕ) (ys : List Mac) (z : Zip) (m : Maybe Zip) →
                    (∀ z₁ → m ≡ just z₁ → plug z₁ ≡ plug z) → (z′ : Zip) →
                    runZ-re ss n ys m ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-re-sound ss n ys z nothing           u z′ ()
    runZ-re-sound ss n ys z (just (zp c b a)) u z′ h =
      trans (≡⇒≈ (Eq.sym (u (zp c b a) Eq.refl)))
      (trans (≡⇒≈ (Eq.cong (revApp b) (Eq.sym (take++drop n a))))
             (runZ-seg-sound ss ys c b (take n a) (drop n a) z′ h))

    runZ-seg-sound : (ss : List Step) (ys : List Mac) (c : ℕ) (b seg rest : List Mac) (z′ : Zip) →
                     runZ-seg ss ys c b seg rest ≡ just z′ → ⟪ revApp b (seg ++ rest) ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-seg-sound ss ys c b seg rest z′ h with sameG seg ys in g
    runZ-seg-sound ss ys c b seg rest z′ h  | true  =
      trans (revApp-cong b (++-congˡ {seg} {ys} rest (by-assoc {⟪ seg ⟫ʷ} {⟪ ys ⟫ʷ} (sameG-ok seg ys g))))
            (runZ-sound ss (zp c b (ys ++ rest)) z′ h)
    runZ-seg-sound ss ys c b seg rest z′ () | false

check-sound : (ss : List Step) (l r : List Mac) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
check-sound ss l r h with runZ ss (zp 0 [] l) in e
check-sound ss l r h  | just z  = trans (runZ-sound ss (zp 0 [] l) z e) (≡⇒≈ (eqLM-sound (plug z) r h))
check-sound ss l r () | nothing

-- The equation of a derivation, checked by running it.
derive : (l r : List Mac) (ss : List Step) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
derive l r ss h = check-sound ss l r h
'''
if TREE != 'Four':
    for a, b in [('-- Four-wire derivations by reflection', '-- Five-wire derivations by reflection'),
                 ('A derivation of Four/D as', f'A derivation of {TREE}/D as'),
                 ('(Four.Letters)', f'({TREE}.Letters)'),
                 ('`scratchpad/four/reflect4.py`', '`scratchpad/five/reflect5.py`'),
                 ('Clifford+CS.Four.Reflect where', f'Clifford+CS.{TREE}.Reflect where'),
                 ('open import Examples.Groups.Clifford+CS.Syntactics\n', SYN + '\n'),
                 ('Clifford+CS.Four.Chain hiding', f'Clifford+CS.{TREE}.Chain hiding'),
                 ('open Assoc (_VRel,_===_ 4)', f'open Assoc ({REL})')]:
        assert body.count(a) == 1, a
        body = body.replace(a, b)
    body = body.replace('Gen 4', f'Gen {W}')
open(F + 'Reflect.agda', 'w', encoding='utf-8', newline='\n').write(body)
print(len(macs), 'letters,', len(gens), 'generators')
