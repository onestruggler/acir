------------------------------------------------------------------------
-- Presentations of groups
--
-- A small proof engine for equations between concrete words, after
-- CCX+HH-TwoLevel.Engine, in any set of relations Γ that derives the
-- local relations (a1)–(d2) of Figure 6 (Local).
--
-- An equation is a pair of letter lists with a derivation (Eqn).  A
-- derivation of a new equation is a list of steps run on the letters:
-- `perm ys` replaces the current list by ys, which must be the same
-- word up to the commutation of letters with disjoint indices (the
-- canonical forms of Presentation.Tactics.Words.Commuting agree), and
-- `rw i e` rewrites the occurrence of lhs e at position i to rhs e.
-- `run` executes the steps, and run-sound turns a successful run into
-- a derivation, so that a proof is a list of steps closed by refl.
--
-- Equations are transformed by sym⁼, by rev⁼ (reversing both sides,
-- as every letter is an involution) and by rot⁼ k m, which reads an
-- equation l = r as the relator l r⁻¹ = ε, rotates it by k letters and
-- splits it after m.  The local relations are equations (ʟ-prefixed).
-- Lists are in operator order, like words: the head acts last.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Word.Base using (Word ; WRel)
import Presentation.Base as PB
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.LocalRelations using (_===ˡ_)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Engine
  {n : ℕ} (Γ : WRel (Gen n)) (loc : ∀ {u v} → u ===ˡ v → PB._≈_ Γ u v) where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.Fin.Base using (Fin ; toℕ ; _<_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe.Base using (Maybe ; just ; nothing ; _>>=_)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _*_ ; _<ᵇ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (does)

open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.Tactics.Words using (commutes ; module Commuting ; module Associative)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
  using (X-gen ; K-gen ; i-gen ; H-gen ; Z-gen)
import Examples.Groups.Real-Clifford+CH-TwoLevel.LocalRelations as L

open Associative using (word-of-list ; lemma-append)
open PB Γ using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
open SR (PP.word-setoid Γ)

------------------------------------------------------------------------
-- Letter lists as words

⟪_⟫ : List (Gen n) → Word (Gen n)
⟪_⟫ = word-of-list

-- Without the trailing ε: ⟪ x ∷ y ∷ [] ⟫ᶠ is [ x ]ʷ • [ y ]ʷ.
⟪_⟫ᶠ : List (Gen n) → Word (Gen n)
⟪ [] ⟫ᶠ           = ε
⟪ x ∷ [] ⟫ᶠ       = [ x ]ʷ
⟪ x ∷ y ∷ zs ⟫ᶠ   = [ x ]ʷ • ⟪ y ∷ zs ⟫ᶠ

⟪++⟫ : (xs ys : List (Gen n)) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
⟪++⟫ xs ys = sym (lemma-append xs ys)

⟪≈⟫ : {xs ys : List (Gen n)} → xs ≡ ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
⟪≈⟫ Eq.refl = refl

flat : (xs : List (Gen n)) → ⟪ xs ⟫ ≈ ⟪ xs ⟫ᶠ
flat [] = refl
flat (x ∷ []) = right-unit
flat (x ∷ y ∷ zs) = cong refl (flat (y ∷ zs))

------------------------------------------------------------------------
-- Equality, order and commutation of letters

eqF : Fin n → Fin n → Bool
eqF a b = does (a FinP.≟ b)

eqF-sound : {a b : Fin n} → eqF a b ≡ true → a ≡ b
eqF-sound {a = a} {b} h with a FinP.≟ b
... | yes e = e
eqF-sound {a = a} {b} () | no _

private
  ∧-l : ∀ {p q} → p ∧ q ≡ true → p ≡ true
  ∧-l {true} _ = Eq.refl
  ∧-r : ∀ {p q} → p ∧ q ≡ true → q ≡ true
  ∧-r {true} h = h

eqG : Gen n → Gen n → Bool
eqG (i-gen a)     (i-gen b)     = eqF a b
eqG (X-gen a b _) (X-gen c d _) = eqF a c ∧ eqF b d
eqG (K-gen a b _) (K-gen c d _) = eqF a c ∧ eqF b d
eqG _             _             = false

eqG-sound : (x y : Gen n) → eqG x y ≡ true → x ≡ y
eqG-sound (i-gen a) (i-gen b) h = Eq.cong i-gen (eqF-sound h)
eqG-sound (X-gen a b p) (X-gen c d q) h
  with eqF-sound {a = a} {c} (∧-l {eqF a c} {eqF b d} h) | eqF-sound {a = b} {d} (∧-r {eqF a c} {eqF b d} h)
... | Eq.refl | Eq.refl = Eq.refl
eqG-sound (K-gen a b p) (K-gen c d q) h
  with eqF-sound {a = a} {c} (∧-l {eqF a c} {eqF b d} h) | eqF-sound {a = b} {d} (∧-r {eqF a c} {eqF b d} h)
... | Eq.refl | Eq.refl = Eq.refl
eqG-sound (i-gen _) (X-gen _ _ _) ()
eqG-sound (i-gen _) (K-gen _ _ _) ()
eqG-sound (X-gen _ _ _) (i-gen _) ()
eqG-sound (X-gen _ _ _) (K-gen _ _ _) ()
eqG-sound (K-gen _ _ _) (i-gen _) ()
eqG-sound (K-gen _ _ _) (X-gen _ _ _) ()

eqL : List (Gen n) → List (Gen n) → Bool
eqL []       []       = true
eqL []       (y ∷ ys) = false
eqL (x ∷ xs) []       = false
eqL (x ∷ xs) (y ∷ ys) = eqG x y ∧ eqL xs ys

eqL-sound : (xs ys : List (Gen n)) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       h = Eq.refl
eqL-sound []       (y ∷ ys) ()
eqL-sound (x ∷ xs) []       ()
eqL-sound (x ∷ xs) (y ∷ ys) h =
  Eq.cong₂ _∷_ (eqG-sound x y (∧-l {eqG x y} {eqL xs ys} h)) (eqL-sound xs ys (∧-r {eqG x y} {eqL xs ys} h))

-- A code, injective on the letters, for the order of the canonical forms.
code : Gen n → ℕ
code (i-gen a)     = 3 * toℕ a
code (X-gen a b _) = 1 + 3 * (toℕ a + n * toℕ b)
code (K-gen a b _) = 2 + 3 * (toℕ a + n * toℕ b)

less : Gen n → Gen n → Bool
less x y = code x <ᵇ code y

-- Letters with disjoint indices commute.
private
  ne? : (a b : Fin n) → Maybe (a ≢ b)
  ne? a b with a FinP.≟ b
  ... | yes _ = nothing
  ... | no ne = just ne

  swap : ∀ {u v} → u ≈ v → v ≈ u
  swap = sym

comm? : (x y : Gen n) → Maybe (commutes Γ x y)
comm? (i-gen a) (i-gen b) = ne? a b >>= λ ab → just (loc (L.b1 ab))
comm? (i-gen a) (X-gen b c p) =
  ne? a b >>= λ ab → ne? a c >>= λ ac → just (loc (L.b2 p ab ac))
comm? (X-gen b c p) (i-gen a) =
  ne? a b >>= λ ab → ne? a c >>= λ ac → just (swap (loc (L.b2 p ab ac)))
comm? (i-gen a) (K-gen b c p) =
  ne? a b >>= λ ab → ne? a c >>= λ ac → just (loc (L.b4 p ab ac))
comm? (K-gen b c p) (i-gen a) =
  ne? a b >>= λ ab → ne? a c >>= λ ac → just (swap (loc (L.b4 p ab ac)))
comm? (X-gen a b p) (X-gen c d q) =
  ne? a c >>= λ ac → ne? a d >>= λ ad → ne? b c >>= λ bc → ne? b d >>= λ bd →
  just (loc (L.b3 p q ac ad bc bd))
comm? (X-gen a b p) (K-gen c d q) =
  ne? a c >>= λ ac → ne? a d >>= λ ad → ne? b c >>= λ bc → ne? b d >>= λ bd →
  just (loc (L.b5 p q ac ad bc bd))
comm? (K-gen c d q) (X-gen a b p) =
  ne? a c >>= λ ac → ne? a d >>= λ ad → ne? b c >>= λ bc → ne? b d >>= λ bd →
  just (swap (loc (L.b5 p q ac ad bc bd)))
comm? (K-gen a b p) (K-gen c d q) =
  ne? a c >>= λ ac → ne? a d >>= λ ad → ne? b c >>= λ bc → ne? b d >>= λ bd →
  just (loc (L.b6 p q ac ad bc bd))

module Canon = Commuting (Gen n) Γ comm? less
open Canon using (comm-canonical ; lemma-comm-canonical)

------------------------------------------------------------------------
-- Every letter is an involution

invol : (x : Gen n) → [ x ]ʷ • [ x ]ʷ ≈ ε
invol (i-gen a)     = loc L.a1
invol (X-gen a b p) = loc (L.a2 p)
invol (K-gen a b p) = loc (L.a3 p)

------------------------------------------------------------------------
-- Reversal

rev : {A : Set} → List A → List A
rev []       = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

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

-- If u • v ≈ ε then u ≈ v⁻¹, the reversal of v.
inverse-of : (xs ys : List (Gen n)) → ⟪ xs ⟫ • ⟪ ys ⟫ ≈ ε → ⟪ xs ⟫ ≈ ⟪ rev ys ⟫
inverse-of xs ys e = begin
  ⟪ xs ⟫                              ≈⟨ sym right-unit ⟩
  ⟪ xs ⟫ • ε                          ≈⟨ cong refl (sym (inv-rev ys)) ⟩
  ⟪ xs ⟫ • (⟪ ys ⟫ • ⟪ rev ys ⟫)      ≈⟨ sym assoc ⟩
  (⟪ xs ⟫ • ⟪ ys ⟫) • ⟪ rev ys ⟫      ≈⟨ trans (cong e refl) left-unit ⟩
  ⟪ rev ys ⟫                          ∎

-- Relators: u • v ≈ ε gives v • u ≈ ε.
rotate-relator : (xs ys : List (Gen n)) → ⟪ xs ⟫ • ⟪ ys ⟫ ≈ ε → ⟪ ys ⟫ • ⟪ xs ⟫ ≈ ε
rotate-relator xs ys e = begin
  ⟪ ys ⟫ • ⟪ xs ⟫                                 ≈⟨ cong refl (inverse-of xs ys e) ⟩
  ⟪ ys ⟫ • ⟪ rev ys ⟫                             ≈⟨ inv-rev ys ⟩
  ε                                               ∎

rev-cong : (xs ys : List (Gen n)) → ⟪ xs ⟫ ≈ ⟪ ys ⟫ → ⟪ rev xs ⟫ ≈ ⟪ rev ys ⟫
rev-cong xs ys e = inverse-of (rev xs) ys (trans (cong refl (sym e)) (rev-inv xs))

------------------------------------------------------------------------
-- Equations

record Eqn : Set where
  constructor eqn
  field
    lhs rhs : List (Gen n)
    prf     : ⟪ lhs ⟫ ≈ ⟪ rhs ⟫

open Eqn public

-- The equation, between words without the trailing ε.
prfᶠ : (e : Eqn) → ⟪ lhs e ⟫ᶠ ≈ ⟪ rhs e ⟫ᶠ
prfᶠ e = trans (sym (flat (lhs e))) (trans (prf e) (flat (rhs e)))

-- An equation from a derivation between the words without trailing ε.
eqnᶠ : (l r : List (Gen n)) → ⟪ l ⟫ᶠ ≈ ⟪ r ⟫ᶠ → Eqn
eqnᶠ l r p = eqn l r (trans (flat l) (trans p (sym (flat r))))

sym⁼ : Eqn → Eqn
sym⁼ (eqn l r p) = eqn r l (sym p)

rev⁼ : Eqn → Eqn
rev⁼ (eqn l r p) = eqn (rev l) (rev r) (rev-cong l r p)

-- The relator l r⁻¹ = ε, rotated by k and split after m.
relator : Eqn → List (Gen n)
relator e = lhs e ++ rev (rhs e)

rotated : ℕ → Eqn → List (Gen n)
rotated k e = drop k (relator e) ++ take k (relator e)

relator-ε : (e : Eqn) → ⟪ relator e ⟫ ≈ ε
relator-ε (eqn l r p) = trans (⟪++⟫ l (rev r)) (trans (cong p refl) (inv-rev r))

split-ε : (k : ℕ) (xs : List (Gen n)) → ⟪ xs ⟫ ≈ ε → ⟪ take k xs ⟫ • ⟪ drop k xs ⟫ ≈ ε
split-ε k xs e = trans (sym (⟪++⟫ (take k xs) (drop k xs))) (trans (⟪≈⟫ (take++drop≡id k xs)) e)

rotated-ε : (k : ℕ) (e : Eqn) → ⟪ rotated k e ⟫ ≈ ε
rotated-ε k e = trans (⟪++⟫ (drop k (relator e)) (take k (relator e)))
  (rotate-relator (take k (relator e)) (drop k (relator e)) (split-ε k (relator e) (relator-ε e)))

rot⁼ : ℕ → ℕ → Eqn → Eqn
rot⁼ k m e = eqn (take m (rotated k e)) (rev (drop m (rotated k e)))
  (inverse-of (take m (rotated k e)) (drop m (rotated k e)) (split-ε m (rotated k e) (rotated-ε k e)))

------------------------------------------------------------------------
-- The local relations as equations

module _ where

  ʟa1 : (a : Fin n) → Eqn
  ʟa1 a = eqnᶠ (i-gen a ∷ i-gen a ∷ []) [] (loc L.a1)

  ʟa2 : (a b : Fin n) .(p : a < b) → Eqn
  ʟa2 a b p = eqnᶠ (X-gen a b p ∷ X-gen a b p ∷ []) [] (loc (L.a2 p))

  ʟa3 : (a b : Fin n) .(p : a < b) → Eqn
  ʟa3 a b p = eqnᶠ (K-gen a b p ∷ K-gen a b p ∷ []) [] (loc (L.a3 p))

  ʟc1 : (a b : Fin n) .(p : a < b) → Eqn
  ʟc1 a b p = eqnᶠ (i-gen a ∷ X-gen a b p ∷ []) (X-gen a b p ∷ i-gen b ∷ []) (loc (L.c1 p))

  ʟc2 : (a b c : Fin n) (p : a < b) (q : b < c) → Eqn
  ʟc2 a b c p q = eqnᶠ (X-gen b c q ∷ X-gen a b p ∷ []) (X-gen a b p ∷ X-gen a c (FinP.<-trans p q) ∷ [])
    (loc (L.c2 p q))

  ʟc3 : (a b c : Fin n) (p : a < b) (q : b < c) → Eqn
  ʟc3 a b c p q = eqnᶠ (X-gen a c (FinP.<-trans p q) ∷ X-gen b c q ∷ []) (X-gen b c q ∷ X-gen a b p ∷ [])
    (loc (L.c3 p q))

  ʟc4 : (a b c : Fin n) (p : a < b) (q : b < c) → Eqn
  ʟc4 a b c p q = eqnᶠ (K-gen b c q ∷ X-gen a b p ∷ []) (X-gen a b p ∷ K-gen a c (FinP.<-trans p q) ∷ [])
    (loc (L.c4 p q))

  ʟc5 : (a b c : Fin n) (p : a < b) (q : b < c) → Eqn
  ʟc5 a b c p q = eqnᶠ (K-gen a c (FinP.<-trans p q) ∷ X-gen b c q ∷ []) (X-gen b c q ∷ K-gen a b p ∷ [])
    (loc (L.c5 p q))

  ʟd1 : (a b : Fin n) .(p : a < b) → Eqn
  ʟd1 a b p = eqnᶠ (i-gen a ∷ i-gen b ∷ K-gen a b p ∷ []) (K-gen a b p ∷ i-gen a ∷ i-gen b ∷ [])
    (loc (L.d1 p))

  ʟd2 : (a b : Fin n) .(p : a < b) → Eqn
  ʟd2 a b p = eqnᶠ (i-gen b ∷ K-gen a b p ∷ []) (K-gen a b p ∷ X-gen a b p ∷ []) (loc (L.d2 p))

------------------------------------------------------------------------
-- Running a derivation

data Step : Set where
  perm : List (Gen n) → Step
  rw   : ℕ → Eqn → Step

rewrite-at : ℕ → Eqn → List (Gen n) → List (Gen n)
rewrite-at i e xs = take i xs ++ (rhs e ++ drop (length (lhs e)) (drop i xs))

matches-at : ℕ → Eqn → List (Gen n) → Bool
matches-at i e xs = eqL (take (length (lhs e)) (drop i xs)) (lhs e)

run : List Step → List (Gen n) → Maybe (List (Gen n))
run []              xs = just xs
run (perm ys ∷ ss)  xs =
  if eqL (comm-canonical xs) (comm-canonical ys) then run ss ys else nothing
run (rw i e ∷ ss)   xs =
  if matches-at i e xs then run ss (rewrite-at i e xs) else nothing

perm-sound : (xs ys : List (Gen n)) → comm-canonical xs ≡ comm-canonical ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
perm-sound xs ys e =
  trans (lemma-comm-canonical xs) (trans (⟪≈⟫ e) (sym (lemma-comm-canonical ys)))

rw-sound : (i : ℕ) (e : Eqn) (xs : List (Gen n)) → matches-at i e xs ≡ true →
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
  m = length (lhs e)
  rest = drop m (drop i xs)

run-sound : (ss : List Step) (xs ys : List (Gen n)) → run ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
run-sound []             xs ys Eq.refl = refl
run-sound (perm zs ∷ ss) xs ys h with eqL (comm-canonical xs) (comm-canonical zs) in c
run-sound (perm zs ∷ ss) xs ys h  | true  = trans (perm-sound xs zs (eqL-sound _ _ c)) (run-sound ss zs ys h)
run-sound (perm zs ∷ ss) xs ys () | false
run-sound (rw i e ∷ ss)  xs ys h with matches-at i e xs in c
run-sound (rw i e ∷ ss)  xs ys h  | true  = trans (rw-sound i e xs c) (run-sound ss (rewrite-at i e xs) ys h)
run-sound (rw i e ∷ ss)  xs ys () | false

-- A derivation: an equation from the steps that turn lhs into rhs.
derive : (l r : List (Gen n)) (ss : List Step) → run ss l ≡ just r → Eqn
derive l r ss h = eqn l r (run-sound ss l r h)
