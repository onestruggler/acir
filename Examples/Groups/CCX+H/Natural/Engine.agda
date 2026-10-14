------------------------------------------------------------------------
-- Presentations of groups
--
-- A small proof engine for equations between concrete circuits of the
-- natural CCX+H calculus, adapted from Examples.Groups.CCX+HH.Natural.Engine
-- (gates X, H, CX, CCX; no scalar).
--
-- An equation is a pair of letter lists with a derivation (Eqn).  A
-- derivation of a new equation is a list of steps run on the letters:
-- `perm ys` replaces the current list by ys, which must be the same
-- word up to the commutation of letters on disjoint wires (the
-- canonical forms of Presentation.Tactics.Words.Commuting agree), and
-- `rw i e` rewrites the occurrence of lhs e at position i to rhs e.
-- `run` executes the steps, and run-sound turns a successful run into
-- a derivation, so that a proof is a list of steps closed by refl.
--
-- Equations are transformed by sym⁼, by lift⁼ (one wire up), by rev⁼
-- (reversing both sides, as every letter is an involution), and by
-- rot⁼ k m, which reads an equation l = r as the relator l r⁻¹ = ε,
-- rotates it by k letters and splits it after m: the first m letters
-- equal the inverse of the rest.  Lists are in operator order, like
-- words: the head acts last.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Natural.Engine where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop ; map)
open import Data.List.Properties using (take++drop≡id ; ++-assoc)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _<ᵇ_ ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.Tactics.Words using (commutes ; module Commuting)
open import Presentation.Tactics.Words using (module Associative)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.CCX+H.Natural.Syntactics

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
gate-eq X-gate   X-gate   = true
gate-eq X-gate   H-gate   = false
gate-eq H-gate   X-gate   = false
gate-eq H-gate   H-gate   = true
gate-eq CX-gate  CX-gate  = true
gate-eq CCX-gate CCX-gate = true

gate-eq-sound : ∀ {k} (a b : Gate k) → gate-eq a b ≡ true → a ≡ b
gate-eq-sound X-gate   X-gate   _ = Eq.refl
gate-eq-sound H-gate   H-gate   _ = Eq.refl
gate-eq-sound CX-gate  CX-gate  _ = Eq.refl
gate-eq-sound CCX-gate CCX-gate _ = Eq.refl
gate-eq-sound X-gate   H-gate   ()
gate-eq-sound H-gate   X-gate   ()

eqG : Gen n → Gen n → Bool
eqG (gate₀ ()) _
eqG (gate₁ a) (gate₁ b) = gate-eq a b
eqG (gate₂ a) (gate₂ b) = gate-eq a b
eqG (gate₃ a) (gate₃ b) = gate-eq a b
eqG (x ↥)     (y ↥)     = eqG x y
eqG _         _         = false

eqG-sound : (x y : Gen n) → eqG x y ≡ true → x ≡ y
eqG-sound (gate₀ ()) _ _
eqG-sound (gate₁ a) (gate₁ b) h = Eq.cong gate₁ (gate-eq-sound a b h)
eqG-sound (gate₂ a) (gate₂ b) h = Eq.cong gate₂ (gate-eq-sound a b h)
eqG-sound (gate₃ a) (gate₃ b) h = Eq.cong gate₃ (gate-eq-sound a b h)
eqG-sound (x ↥)     (y ↥)     h = Eq.cong _↥ (eqG-sound x y h)
eqG-sound (gate₁ a) (gate₀ ()) _
eqG-sound (gate₁ a) (gate₂ b) ()
eqG-sound (gate₁ a) (gate₃ b) ()
eqG-sound (gate₁ a) (y ↥)     ()
eqG-sound (gate₂ a) (gate₀ ()) _
eqG-sound (gate₂ a) (gate₁ b) ()
eqG-sound (gate₂ a) (gate₃ b) ()
eqG-sound (gate₂ a) (y ↥)     ()
eqG-sound (gate₃ a) (gate₀ ()) _
eqG-sound (gate₃ a) (gate₁ b) ()
eqG-sound (gate₃ a) (gate₂ b) ()
eqG-sound (gate₃ a) (y ↥)     ()
eqG-sound (x ↥)     (gate₀ ()) _
eqG-sound (x ↥)     (gate₁ b) ()
eqG-sound (x ↥)     (gate₂ b) ()
eqG-sound (x ↥)     (gate₃ b) ()

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
code (gate₀ ())
code (gate₁ X-gate)   = 0
code (gate₁ H-gate)   = 1
code (gate₂ CX-gate)  = 2
code (gate₃ CCX-gate) = 3
code (g ↥)            = 4 + code g

less : Gen n → Gen n → Bool
less x y = code x <ᵇ code y

-- Letters on disjoint wires commute.
comm? : (x y : Gen n) → Maybe (commutes (n VRel,_===_) x y)
comm? (gate₁ h)     (y ↥)         = just (PB.sym (PB.axiom (comm₁ h y)))
comm? (y ↥)         (gate₁ h)     = just (PB.axiom (comm₁ h y))
comm? (gate₂ h)     ((y ↥) ↥)     = just (PB.sym (PB.axiom (comm₂ h y)))
comm? ((y ↥) ↥)     (gate₂ h)     = just (PB.axiom (comm₂ h y))
comm? (gate₃ h)     (((y ↥) ↥) ↥) = just (PB.sym (PB.axiom (comm₃ h y)))
comm? (((y ↥) ↥) ↥) (gate₃ h)     = just (PB.axiom (comm₃ h y))
comm? (x ↥)         (y ↥)         with comm? x y
... | just p  = just (lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) p)
... | nothing = nothing
comm? _             _             = nothing

module Canon {n : ℕ} = Commuting (Gen n) (n VRel,_===_) comm? less
open Canon using (comm-canonical ; lemma-comm-canonical)

------------------------------------------------------------------------
-- Every letter is an involution

invol : (x : Gen n) → n ⊢ [ x ]ʷ • [ x ]ʷ ≈ ε
invol (gate₀ ())
invol (gate₁ X-gate)   = PB.axiom (srel X²)
invol (gate₁ H-gate)   = PB.axiom (srel H²)
invol (gate₂ CX-gate)  = PB.axiom (srel CX²)
invol (gate₃ CCX-gate) = PB.axiom (srel CCX²)
invol (x ↥)            = lemma-cong↑ ([ x ]ʷ • [ x ]ʷ) ε (invol x)

------------------------------------------------------------------------
-- Reversal

rev : {A : Set} → List A → List A
rev []       = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

module _ {n : ℕ} where

  open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  rev-inv : (xs : List (Gen n)) → ⟪ rev xs ⟫ • ⟪ xs ⟫ ≈ ε
  rev-inv []       = left-unit
  rev-inv (x ∷ xs) = begin
    ⟪ rev xs ++ (x ∷ []) ⟫ • ([ x ]ʷ • ⟪ xs ⟫)        ≈⟨ cong (⟪++⟫ (rev xs) (x ∷ [])) refl ⟩
    (⟪ rev xs ⟫ • ([ x ]ʷ • ε)) • ([ x ]ʷ • ⟪ xs ⟫)   ≈⟨ cong (cong refl right-unit) refl ⟩
    (⟪ rev xs ⟫ • [ x ]ʷ) • ([ x ]ʷ • ⟪ xs ⟫)         ≈⟨ assoc ⟩
    ⟪ rev xs ⟫ • ([ x ]ʷ • ([ x ]ʷ • ⟪ xs ⟫))         ≈⟨ cong refl (sym assoc) ⟩
    ⟪ rev xs ⟫ • (([ x ]ʷ • [ x ]ʷ) • ⟪ xs ⟫)         ≈⟨ cong refl (trans (cong (invol x) refl) left-unit) ⟩
    ⟪ rev xs ⟫ • ⟪ xs ⟫                               ≈⟨ rev-inv xs ⟩
    ε                                                 ∎
    where open SR (PP.word-setoid (n VRel,_===_))

  inv-rev : (xs : List (Gen n)) → ⟪ xs ⟫ • ⟪ rev xs ⟫ ≈ ε
  inv-rev []       = left-unit
  inv-rev (x ∷ xs) = begin
    ([ x ]ʷ • ⟪ xs ⟫) • ⟪ rev xs ++ (x ∷ []) ⟫        ≈⟨ cong refl (⟪++⟫ (rev xs) (x ∷ [])) ⟩
    ([ x ]ʷ • ⟪ xs ⟫) • (⟪ rev xs ⟫ • ([ x ]ʷ • ε))   ≈⟨ cong refl (cong refl right-unit) ⟩
    ([ x ]ʷ • ⟪ xs ⟫) • (⟪ rev xs ⟫ • [ x ]ʷ)         ≈⟨ assoc ⟩
    [ x ]ʷ • (⟪ xs ⟫ • (⟪ rev xs ⟫ • [ x ]ʷ))         ≈⟨ cong refl (sym assoc) ⟩
    [ x ]ʷ • ((⟪ xs ⟫ • ⟪ rev xs ⟫) • [ x ]ʷ)         ≈⟨ cong refl (trans (cong (inv-rev xs) refl) left-unit) ⟩
    [ x ]ʷ • [ x ]ʷ                                   ≈⟨ invol x ⟩
    ε                                                 ∎
    where open SR (PP.word-setoid (n VRel,_===_))

  -- If u • v ≈ ε then u ≈ v⁻¹, the reversal of v.
  inverse-of : (xs ys : List (Gen n)) → ⟪ xs ⟫ • ⟪ ys ⟫ ≈ ε → ⟪ xs ⟫ ≈ ⟪ rev ys ⟫
  inverse-of xs ys e = begin
    ⟪ xs ⟫                              ≈⟨ sym right-unit ⟩
    ⟪ xs ⟫ • ε                          ≈⟨ cong refl (sym (inv-rev ys)) ⟩
    ⟪ xs ⟫ • (⟪ ys ⟫ • ⟪ rev ys ⟫)      ≈⟨ sym assoc ⟩
    (⟪ xs ⟫ • ⟪ ys ⟫) • ⟪ rev ys ⟫      ≈⟨ trans (cong e refl) left-unit ⟩
    ⟪ rev ys ⟫                          ∎
    where open SR (PP.word-setoid (n VRel,_===_))

  -- Relators: u • v ≈ ε gives v • u ≈ ε.
  rotate-relator : (xs ys : List (Gen n)) → ⟪ xs ⟫ • ⟪ ys ⟫ ≈ ε → ⟪ ys ⟫ • ⟪ xs ⟫ ≈ ε
  rotate-relator xs ys e = begin
    ⟪ ys ⟫ • ⟪ xs ⟫                                 ≈⟨ cong refl (inverse-of xs ys e) ⟩
    ⟪ ys ⟫ • ⟪ rev ys ⟫                             ≈⟨ inv-rev ys ⟩
    ε                                               ∎
    where open SR (PP.word-setoid (n VRel,_===_))

  rev-cong : (xs ys : List (Gen n)) → ⟪ xs ⟫ ≈ ⟪ ys ⟫ → ⟪ rev xs ⟫ ≈ ⟪ rev ys ⟫
  rev-cong xs ys e = begin
    ⟪ rev xs ⟫                                  ≈⟨ inverse-of (rev xs) ys (trans (cong refl (sym e)) (rev-inv xs)) ⟩
    ⟪ rev ys ⟫                                  ∎
    where open SR (PP.word-setoid (n VRel,_===_))

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

rev⁼ : Eqn n → Eqn n
rev⁼ (eqn l r p) = eqn (rev l) (rev r) (rev-cong l r p)

-- Shifting the letters shifts the word.
⟪map↥⟫ : (xs : List (Gen n)) → ⟪ map _↥ xs ⟫ ≡ ⟪ xs ⟫ ↑
⟪map↥⟫ []       = Eq.refl
⟪map↥⟫ (x ∷ xs) = Eq.cong ([ x ↥ ]ʷ •_) (⟪map↥⟫ xs)

-- One wire up.
lift-gen : Gen n → Gen (₁₊ n)
lift-gen g = g ↥

lift⁼ : Eqn n → Eqn (₁₊ n)
lift⁼ (eqn l r p) = eqn (map lift-gen l) (map lift-gen r)
  (PB.trans (⟪≈'⟫ (⟪map↥⟫ l)) (PB.trans (lemma-cong↑ ⟪ l ⟫ ⟪ r ⟫ p) (PB.sym (⟪≈'⟫ (⟪map↥⟫ r)))))
  where
  ⟪≈'⟫ : ∀ {m} {w v : Circuit m} → w ≡ v → m ⊢ w ≈ v
  ⟪≈'⟫ Eq.refl = PB.refl

-- The relator l r⁻¹ = ε, rotated by k and split after m.
relator : Eqn n → List (Gen n)
relator e = lhs e ++ rev (rhs e)

rotated : ℕ → Eqn n → List (Gen n)
rotated k e = drop k (relator e) ++ take k (relator e)

module _ {n : ℕ} where

  open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  relator-ε : (e : Eqn n) → ⟪ relator e ⟫ ≈ ε
  relator-ε (eqn l r p) = trans (⟪++⟫ l (rev r)) (trans (cong p refl) (inv-rev r))

  split-ε : (k : ℕ) (xs : List (Gen n)) → ⟪ xs ⟫ ≈ ε → ⟪ take k xs ⟫ • ⟪ drop k xs ⟫ ≈ ε
  split-ε k xs e = trans (sym (⟪++⟫ (take k xs) (drop k xs))) (trans (⟪≈⟫ (take++drop≡id k xs)) e)

  rotated-ε : (k : ℕ) (e : Eqn n) → ⟪ rotated k e ⟫ ≈ ε
  rotated-ε k e = trans (⟪++⟫ (drop k (relator e)) (take k (relator e)))
    (rotate-relator (take k (relator e)) (drop k (relator e)) (split-ε k (relator e) (relator-ε e)))

rot⁼ : ℕ → ℕ → Eqn n → Eqn n
rot⁼ k m e = eqn (take m (rotated k e)) (rev (drop m (rotated k e)))
  (inverse-of (take m (rotated k e)) (drop m (rotated k e)) (split-ε m (rotated k e) (rotated-ε k e)))

------------------------------------------------------------------------
-- Running a derivation

data Step (n : ℕ) : Set where
  perm : List (Gen n) → Step n
  rw   : ℕ → Eqn n → Step n

rewrite-at : ℕ → Eqn n → List (Gen n) → List (Gen n)
rewrite-at i e xs = take i xs ++ (rhs e ++ drop (length (lhs e)) (drop i xs))

matches-at : ℕ → Eqn n → List (Gen n) → Bool
matches-at i e xs = eqL (take (length (lhs e)) (drop i xs)) (lhs e)

run : List (Step n) → List (Gen n) → Maybe (List (Gen n))
run []              xs = just xs
run (perm ys ∷ ss)  xs =
  if eqL (comm-canonical xs) (comm-canonical ys) then run ss ys else nothing
run (rw i e ∷ ss)   xs =
  if matches-at i e xs then run ss (rewrite-at i e xs) else nothing

module _ {n : ℕ} where

  open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  perm-sound : (xs ys : List (Gen n)) → comm-canonical xs ≡ comm-canonical ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  perm-sound xs ys e =
    trans (lemma-comm-canonical xs) (trans (⟪≈⟫ e) (sym (lemma-comm-canonical ys)))

  rw-sound : (i : ℕ) (e : Eqn n) (xs : List (Gen n)) → matches-at i e xs ≡ true →
             ⟪ xs ⟫ ≈ ⟪ rewrite-at i e xs ⟫
  rw-sound i e xs h = begin
    ⟪ xs ⟫                                          ≈⟨ ⟪≈⟫ (Eq.sym (take++drop≡id i xs)) ⟩
    ⟪ take i xs ++ drop i xs ⟫                      ≈⟨ ⟪++⟫ (take i xs) (drop i xs) ⟩
    ⟪ take i xs ⟫ • ⟪ drop i xs ⟫                   ≈⟨ cong refl (⟪≈⟫ (Eq.sym (take++drop≡id m (drop i xs)))) ⟩
    ⟪ take i xs ⟫ • ⟪ take m (drop i xs) ++ rest ⟫  ≈⟨ cong refl (⟪++⟫ (take m (drop i xs)) rest) ⟩
    ⟪ take i xs ⟫ • (⟪ take m (drop i xs) ⟫ • ⟪ rest ⟫)
                                                    ≈⟨ cong refl (cong (⟪≈⟫ (eqL-sound _ _ h)) refl) ⟩
    ⟪ take i xs ⟫ • (⟪ lhs e ⟫ • ⟪ rest ⟫)          ≈⟨ cong refl (cong (prf e) refl) ⟩
    ⟪ take i xs ⟫ • (⟪ rhs e ⟫ • ⟪ rest ⟫)          ≈⟨ cong refl (sym (⟪++⟫ (rhs e) rest)) ⟩
    ⟪ take i xs ⟫ • ⟪ rhs e ++ rest ⟫               ≈⟨ sym (⟪++⟫ (take i xs) (rhs e ++ rest)) ⟩
    ⟪ rewrite-at i e xs ⟫                           ∎
    where
    open SR (PP.word-setoid (n VRel,_===_))
    m = length (lhs e)
    rest = drop m (drop i xs)

  run-sound : (ss : List (Step n)) (xs ys : List (Gen n)) → run ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  run-sound []             xs ys Eq.refl = refl
  run-sound (perm zs ∷ ss) xs ys h with eqL (comm-canonical xs) (comm-canonical zs) in c
  run-sound (perm zs ∷ ss) xs ys h  | true  = trans (perm-sound xs zs (eqL-sound _ _ c)) (run-sound ss zs ys h)
  run-sound (perm zs ∷ ss) xs ys () | false
  run-sound (rw i e ∷ ss)  xs ys h with matches-at i e xs in c
  run-sound (rw i e ∷ ss)  xs ys h  | true  = trans (rw-sound i e xs c) (run-sound ss (rewrite-at i e xs) ys h)
  run-sound (rw i e ∷ ss)  xs ys () | false

-- A derivation: an equation from the steps that turn lhs into rhs.
derive : (l r : List (Gen n)) (ss : List (Step n)) → run ss l ≡ just r → Eqn n
derive l r ss h = eqn l r (run-sound ss l r h)

------------------------------------------------------------------------
-- Cancelling a common prefix

module _ {n : ℕ} where

  open PB (n VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  cancelˡ : (k l r : List (Gen n)) → ⟪ k ++ l ⟫ ≈ ⟪ k ++ r ⟫ → ⟪ l ⟫ ≈ ⟪ r ⟫
  cancelˡ k l r e = begin
    ⟪ l ⟫                               ≈⟨ sym left-unit ⟩
    ε • ⟪ l ⟫                           ≈⟨ cong (sym (rev-inv k)) refl ⟩
    (⟪ rev k ⟫ • ⟪ k ⟫) • ⟪ l ⟫         ≈⟨ assoc ⟩
    ⟪ rev k ⟫ • (⟪ k ⟫ • ⟪ l ⟫)         ≈⟨ cong refl (trans (sym (⟪++⟫ k l)) (trans e (⟪++⟫ k r))) ⟩
    ⟪ rev k ⟫ • (⟪ k ⟫ • ⟪ r ⟫)         ≈⟨ sym assoc ⟩
    (⟪ rev k ⟫ • ⟪ k ⟫) • ⟪ r ⟫         ≈⟨ cong (rev-inv k) refl ⟩
    ε • ⟪ r ⟫                           ≈⟨ left-unit ⟩
    ⟪ r ⟫                               ∎
    where open SR (PP.word-setoid (n VRel,_===_))

-- The equation l = r from two derivations k l ⇝ m and k r ⇝ m.
by-cancel : (k l r : List (Gen n)) (p q : Eqn n) →
            lhs p ≡ k ++ l → lhs q ≡ k ++ r → rhs p ≡ rhs q → Eqn n
by-cancel {n} k l r p q ep eq er = eqn l r (cancelˡ k l r
  (PB.trans (⟪≈⟫ (Eq.sym ep)) (PB.trans (prf p) (PB.trans (⟪≈⟫ er)
    (PB.trans (PB.sym (prf q)) (⟪≈⟫ eq))))))
