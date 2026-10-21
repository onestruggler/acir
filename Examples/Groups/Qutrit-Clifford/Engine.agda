------------------------------------------------------------------------
-- Presentations of groups
--
-- A small proof engine for equations between concrete circuits
--
-- An equation is a pair of letter lists with a derivation (Eqn).  A
-- derivation of a new equation is a list of steps run on the letters:
-- `perm ys` replaces the current list by ys, which must be the same
-- word up to the commutation of letters on disjoint wires (the
-- canonical forms of Presentation.Tactics.Words.Commuting agree), and
-- `rw i e` rewrites the occurrence of lhs e at position i to rhs e.
-- `runs` executes the steps, and run-sound turns a successful run into
-- a derivation, so that a proof is a list of steps closed by refl.
--
-- Equations are transformed by sym⁼ and by lift⁼ (one wire up).
-- Lists are in operator order, like words: the head acts last.  This is
-- Examples.Groups.Qubit-Clifford.Engine over the qutrit gates.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Engine where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop ; map)
open import Data.List.Properties using (take++drop≡id ; ++-assoc)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _<ᵇ_ ; _≡ᵇ_ ; pred ; _∸_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.Tactics.Words using (commutes ; module Commuting)
open import Presentation.Tactics.Words using (module Associative)

open import Notations using (₁₊ ; ₂₊)
open import Examples.Groups.Qutrit-Clifford.Syntactics

open Associative using (word-of-list ; lemma-append)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Letter lists as circuits

⟪_⟫ : List (Gen n) → Circuit n
⟪_⟫ = word-of-list

module _ {n : ℕ} where

  open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  ⟪++⟫ : (xs ys : List (Gen n)) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
  ⟪++⟫ xs ys = sym (lemma-append xs ys)

  -- Congruence on the right of a fixed prefix, and on the left of a
  -- fixed suffix.
  ⟪≈⟫ : {xs ys : List (Gen n)} → xs ≡ ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  ⟪≈⟫ Eq.refl = refl

------------------------------------------------------------------------
-- Equality, order and commutation of letters

gate-eq : ∀ {k} → Gate k → Gate k → Bool
gate-eq ν-gate  ν-gate  = true
gate-eq H-gate  H-gate  = true
gate-eq H-gate  S-gate  = false
gate-eq S-gate  H-gate  = false
gate-eq S-gate  S-gate  = true
gate-eq CZ-gate CZ-gate = true

gate-eq-sound : ∀ {k} (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
gate-eq-sound ν-gate  ν-gate  _ = Eq.refl
gate-eq-sound H-gate  H-gate  _ = Eq.refl
gate-eq-sound S-gate  S-gate  _ = Eq.refl
gate-eq-sound CZ-gate CZ-gate _ = Eq.refl
gate-eq-sound H-gate  S-gate  ()
gate-eq-sound S-gate  H-gate  ()

eqG : Gen n → Gen n → Bool
eqG (gate₀ a) (gate₀ b) = gate-eq a b
eqG (gate₀ a) (gate₁ b) = false
eqG (gate₀ a) (gate₂ b) = false
eqG (gate₀ a) (y ↥)     = false
eqG (gate₁ a) (gate₀ b) = false
eqG (gate₁ a) (gate₁ b) = gate-eq a b
eqG (gate₁ a) (gate₂ b) = false
eqG (gate₁ a) (y ↥)     = false
eqG (gate₂ a) (gate₀ b) = false
eqG (gate₂ a) (gate₁ b) = false
eqG (gate₂ a) (gate₂ b) = gate-eq a b
eqG (gate₂ a) (y ↥)     = false
eqG (x ↥)     (gate₀ b) = false
eqG (x ↥)     (gate₁ b) = false
eqG (x ↥)     (gate₂ b) = false
eqG (x ↥)     (y ↥)     = eqG x y

eqG-sound : (x y : Gen n) → eqG x y ≡ true → x ≡ y
eqG-sound (gate₀ a) (gate₀ b) h = Eq.cong gate₀ (gate-eq-sound a b h)
eqG-sound (gate₁ a) (gate₁ b) h = Eq.cong gate₁ (gate-eq-sound a b h)
eqG-sound (gate₂ a) (gate₂ b) h = Eq.cong gate₂ (gate-eq-sound a b h)
eqG-sound (x ↥)     (y ↥)     h = Eq.cong _↥ (eqG-sound x y h)
eqG-sound (gate₀ a) (gate₁ b) ()
eqG-sound (gate₀ a) (gate₂ b) ()
eqG-sound (gate₀ a) (y ↥)     ()
eqG-sound (gate₁ a) (gate₀ b) ()
eqG-sound (gate₁ a) (gate₂ b) ()
eqG-sound (gate₁ a) (y ↥)     ()
eqG-sound (gate₂ a) (gate₀ b) ()
eqG-sound (gate₂ a) (gate₁ b) ()
eqG-sound (gate₂ a) (y ↥)     ()
eqG-sound (x ↥)     (gate₀ b) ()
eqG-sound (x ↥)     (gate₁ b) ()
eqG-sound (x ↥)     (gate₂ b) ()

eqL : List (Gen n) → List (Gen n) → Bool
eqL []       []       = true
eqL []       (y ∷ ys) = false
eqL (x ∷ xs) []       = false
eqL (x ∷ xs) (y ∷ ys) = eqG x y ∧ eqL xs ys

eqL-sound : (xs ys : List (Gen n)) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       h = Eq.refl
eqL-sound []       (y ∷ ys) ()
eqL-sound (x ∷ xs) []       ()
eqL-sound (x ∷ xs) (y ∷ ys) h with eqG x y in e
eqL-sound (x ∷ xs) (y ∷ ys) h  | true  = Eq.cong₂ _∷_ (eqG-sound x y e) (eqL-sound xs ys h)
eqL-sound (x ∷ xs) (y ∷ ys) () | false

-- An injective code, for the order of the canonical forms.
code : Gen n → ℕ
code (gate₀ ν-gate)   = 0
code (gate₁ H-gate)   = 1
code (gate₁ S-gate)   = 2
code (gate₂ CZ-gate)  = 3
code (g ↥)            = 4 + code g

less : Gen n → Gen n → Bool
less x y = code x <ᵇ code y

-- Letters on disjoint wires commute; the scalar commutes with all.
comm? : (x y : Gen n) → Maybe (commutes (n VRel,_===_) x y)
comm? x             (gate₀ h)     = just (comm₀ h x)
comm? (gate₀ h)     y             = just (PB.sym (comm₀ h y))
comm? (gate₁ h)     (y ↥)         = just (PB.sym (PB.axiom (comm₁ h y)))
comm? (y ↥)         (gate₁ h)     = just (PB.axiom (comm₁ h y))
comm? (gate₂ h)     ((y ↥) ↥)     = just (PB.sym (PB.axiom (comm₂ h y)))
comm? ((y ↥) ↥)     (gate₂ h)     = just (PB.axiom (comm₂ h y))
comm? (x ↥)         (y ↥)         with comm? x y
... | just p  = just (lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) p)
... | nothing = nothing
comm? _             _             = nothing

module Canon {n : ℕ} = Commuting (Gen n) (n VRel,_===_) comm? less
open Canon using (comm-canonical ; lemma-comm-canonical)

------------------------------------------------------------------------
-- Equations

record Eqn (n : ℕ) : Set where
  constructor eqn
  field
    lhs rhs : List (Gen n)
    prf     : n ⊢ ⟪ lhs ⟫ ≈ ⟪ rhs ⟫

open Eqn public

sym⁼ : Eqn n → Eqn n
sym⁼ (eqn l r p) = eqn r l (PB.sym p)

-- Shifting the letters shifts the word.
⟪map↥⟫ : (xs : List (Gen n)) → ⟪ map _↥ xs ⟫ ≡ ⟪ xs ⟫ ↑
⟪map↥⟫ []       = Eq.refl
⟪map↥⟫ (x ∷ xs) = Eq.cong ([ x ↥ ]ʷ •_) (⟪map↥⟫ xs)

-- One wire up.  The scalar stays the scalar of the wider circuit
-- (ω↑=ω), so that lifted equations still match the letters of a word.
lift-gen : Gen n → Gen (₁₊ n)
lift-gen (gate₀ h) = gate₀ h
lift-gen g         = g ↥

module _ {n : ℕ} where

  open PB ((₁₊ n) VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong)

  ⟪map-lift⟫ : (xs : List (Gen n)) → ⟪ map lift-gen xs ⟫ ≈ ⟪ xs ⟫ ↑
  ⟪map-lift⟫ []               = refl
  ⟪map-lift⟫ (gate₀ h ∷ xs)   = cong (sym (PB.axiom (ω↑=ω h))) (⟪map-lift⟫ xs)
  ⟪map-lift⟫ (gate₁ h ∷ xs)   = cong refl (⟪map-lift⟫ xs)
  ⟪map-lift⟫ (gate₂ h ∷ xs)   = cong refl (⟪map-lift⟫ xs)
  ⟪map-lift⟫ ((g ↥) ∷ xs)     = cong refl (⟪map-lift⟫ xs)

lift⁼ : Eqn n → Eqn (₁₊ n)
lift⁼ (eqn l r p) = eqn (map lift-gen l) (map lift-gen r)
  (PB.trans (⟪map-lift⟫ l) (PB.trans (lemma-cong↑ ⟪ l ⟫ ⟪ r ⟫ p) (PB.sym (⟪map-lift⟫ r))))

------------------------------------------------------------------------
-- Running a derivation

data Step (n : ℕ) : Set where
  perm : List (Gen n) → Step n
  rw   : ℕ → Eqn n → Step n

-- The word being rewritten is kept as a zipper: the letters before the
-- focus, last first, and the letters from it on, with the index of the
-- focus.  `rw i e` moves the focus to i, which costs the distance from
-- where the last step was: the derivations of the box relations
-- rewrite words of over a thousand letters at positions 870 on average
-- but 87 from the one before.  The equation's sides and the parts of
-- the word are passed on as arguments (runZ-rw, runZ-at), which Agda's
-- evaluator computes once however often they are used.
record Zip (n : ℕ) : Set where
  constructor zp
  field
    at     : ℕ
    before : List (Gen n)
    after  : List (Gen n)

-- before reversed onto after.
revApp : List (Gen n) → List (Gen n) → List (Gen n)
revApp []       ys = ys
revApp (x ∷ xs) ys = revApp xs (x ∷ ys)

unzip : Zip n → List (Gen n)
unzip (zp _ b a) = revApp b a

left right : ℕ → Zip n → Maybe (Zip n)
left zero    z               = just z
left (suc k) (zp c (x ∷ b) a) = left k (zp (pred c) b (x ∷ a))
left (suc k) (zp c [] a)      = nothing
right zero    z               = just z
right (suc k) (zp c b (x ∷ a)) = right k (zp (suc c) (x ∷ b) a)
right (suc k) (zp c b [])      = nothing

moveTo : ℕ → Zip n → Maybe (Zip n)
moveTo i (zp c b a) = if i <ᵇ c then left (c ∸ i) (zp c b a) else right (i ∸ c) (zp c b a)

mutual
  runZ : List (Step n) → Zip n → Maybe (Zip n)
  runZ []              z = just z
  runZ (perm ys ∷ ss)  z =
    if eqL (comm-canonical (unzip z)) (comm-canonical ys) then runZ ss (zp 0 [] ys) else nothing
  runZ (rw i e ∷ ss)   z = runZ-rw ss (lhs e) (rhs e) (moveTo i z)

  runZ-rw : List (Step n) → (l r : List (Gen n)) → Maybe (Zip n) → Maybe (Zip n)
  runZ-rw ss l r nothing            = nothing
  runZ-rw ss l r (just (zp c b a))  = runZ-at ss (length l) l r c b a

  runZ-at : List (Step n) → ℕ → (l r : List (Gen n)) → ℕ → (b a : List (Gen n)) → Maybe (Zip n)
  runZ-at ss m l r c b a =
    if eqL (take m a) l then runZ ss (zp c b (r ++ drop m a)) else nothing

-- Whether the steps turn l into r, as one Boolean: Agda decides it in
-- one evaluation, where comparing the lists by conversion evaluates
-- each letter of the result anew.
okZ : List (Gen n) → Maybe (Zip n) → Bool
okZ r (just z) = eqL (unzip z) r
okZ r nothing  = false

runs : List (Step n) → List (Gen n) → List (Gen n) → Bool
runs ss l r = okZ r (runZ ss (zp 0 [] l))

module _ {n : ℕ} where

  open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  perm-sound : (xs ys : List (Gen n)) → comm-canonical xs ≡ comm-canonical ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  perm-sound xs ys e =
    trans (lemma-comm-canonical xs) (trans (⟪≈⟫ e) (sym (lemma-comm-canonical ys)))

  -- Moving the focus keeps the word.
  left-un : (k : ℕ) (z z' : Zip n) → left k z ≡ just z' → unzip z' ≡ unzip z
  left-un zero    z                z' Eq.refl = Eq.refl
  left-un (suc k) (zp c (x ∷ b) a) z' h       = left-un k (zp (pred c) b (x ∷ a)) z' h
  left-un (suc k) (zp c [] a)      z' ()

  right-un : (k : ℕ) (z z' : Zip n) → right k z ≡ just z' → unzip z' ≡ unzip z
  right-un zero    z                z' Eq.refl = Eq.refl
  right-un (suc k) (zp c b (x ∷ a)) z' h       = right-un k (zp (suc c) (x ∷ b) a) z' h
  right-un (suc k) (zp c b [])      z' ()

  moveTo-un : (i : ℕ) (z z' : Zip n) → moveTo i z ≡ just z' → unzip z' ≡ unzip z
  moveTo-un i (zp c b a) z' h with i <ᵇ c
  ... | true  = left-un (c ∸ i) (zp c b a) z' h
  ... | false = right-un (i ∸ c) (zp c b a) z' h

  revApp-cong : (b : List (Gen n)) {x y : List (Gen n)} → ⟪ x ⟫ ≈ ⟪ y ⟫ → ⟪ revApp b x ⟫ ≈ ⟪ revApp b y ⟫
  revApp-cong []      e = e
  revApp-cong (g ∷ b) e = revApp-cong b (cong refl e)

  -- A rewrite at the focus.
  at-sound : (e : Eqn n) (a : List (Gen n)) → eqL (take (length (lhs e)) a) (lhs e) ≡ true →
             ⟪ a ⟫ ≈ ⟪ rhs e ++ drop (length (lhs e)) a ⟫
  at-sound e a h = begin
    ⟪ a ⟫                            ≈⟨ ⟪≈⟫ (Eq.sym (take++drop≡id m a)) ⟩
    ⟪ take m a ++ drop m a ⟫         ≈⟨ ⟪++⟫ (take m a) (drop m a) ⟩
    ⟪ take m a ⟫ • ⟪ drop m a ⟫      ≈⟨ cong (⟪≈⟫ (eqL-sound _ _ h)) refl ⟩
    ⟪ lhs e ⟫ • ⟪ drop m a ⟫         ≈⟨ cong (prf e) refl ⟩
    ⟪ rhs e ⟫ • ⟪ drop m a ⟫         ≈⟨ sym (⟪++⟫ (rhs e) (drop m a)) ⟩
    ⟪ rhs e ++ drop m a ⟫            ∎
    where
    open SR (PP.word-setoid (n VRel,_===_))
    m = length (lhs e)

  mutual
    runZ-sound : (ss : List (Step n)) (z z' : Zip n) → runZ ss z ≡ just z' → ⟪ unzip z ⟫ ≈ ⟪ unzip z' ⟫
    runZ-sound []             z z' Eq.refl = refl
    runZ-sound (perm ys ∷ ss) z z' h with eqL (comm-canonical (unzip z)) (comm-canonical ys) in c
    runZ-sound (perm ys ∷ ss) z z' h  | true  =
      trans (perm-sound (unzip z) ys (eqL-sound _ _ c)) (runZ-sound ss (zp 0 [] ys) z' h)
    runZ-sound (perm ys ∷ ss) z z' () | false
    runZ-sound (rw i e ∷ ss)  z z' h with moveTo i z in mv
    runZ-sound (rw i e ∷ ss)  z z' () | nothing
    runZ-sound (rw i e ∷ ss)  z z' h  | just (zp c b a) =
      trans (⟪≈⟫ (Eq.sym (moveTo-un i z (zp c b a) mv))) (runZ-at-sound e ss c b a z' h)

    runZ-at-sound : (e : Eqn n) (ss : List (Step n)) (c : ℕ) (b a : List (Gen n)) (z' : Zip n) →
                    runZ-at ss (length (lhs e)) (lhs e) (rhs e) c b a ≡ just z' →
                    ⟪ revApp b a ⟫ ≈ ⟪ unzip z' ⟫
    runZ-at-sound e ss c b a z' h with eqL (take (length (lhs e)) a) (lhs e) in q
    runZ-at-sound e ss c b a z' h  | true  =
      trans (revApp-cong b (at-sound e a q)) (runZ-sound ss (zp c b (rhs e ++ drop (length (lhs e)) a)) z' h)
    runZ-at-sound e ss c b a z' () | false

  run-sound : (ss : List (Step n)) (xs ys : List (Gen n)) → runs ss xs ys ≡ true → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  run-sound ss xs ys h with runZ ss (zp 0 [] xs) in q
  run-sound ss xs ys h  | just z  = trans (runZ-sound ss (zp 0 [] xs) z q) (⟪≈⟫ (eqL-sound _ _ h))
  run-sound ss xs ys () | nothing

-- A derivation: an equation from the steps that turn lhs into rhs.
derive : (l r : List (Gen n)) (ss : List (Step n)) → runs ss l r ≡ true → Eqn n
derive l r ss h = eqn l r (run-sound ss l r h)

