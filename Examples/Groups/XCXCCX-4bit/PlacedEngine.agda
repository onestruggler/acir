------------------------------------------------------------------------
-- Presentations of groups
--
-- A proof engine over placed letters on four wires
--
-- Examples.Independence.Engine for the alphabet PG of Placed.  An
-- equation is a pair of lists of placed letters with a derivation
-- between their circuits (Eqnᵖ: 4 ⊢ ι* lhs⁼ ≈ ι* rhs⁼), and a new one is
-- derived by a list of steps run on the letters, `derive l r steps
-- refl`:
--
--   perm ys         the same word up to commuting letters on disjoint
--                   wires (Placed.disj-comm), compared by the canonical
--                   forms of Presentation.Tactics.Words.Commuting;
--   rw i e          rewrite the occurrence of lhs⁼ e at position i to
--                   rhs⁼ e;
--   narrow i k ys   replace the k letters at position i by ys, where
--                   both lie on three of the four wires (the first of
--                   wires 3, 2, 1, 0 that they leave alone) and have the
--                   same function: decided by evaluating ⟦_⟧ᵖ*, and
--                   sound by completeness on three wires
--                   (Narrow3.narrowᵖ).
--
-- Equations: sym⁼, relabel⁼ (along any permutation of the wires), r7⁼
-- (rule (7), Placed.lhs₇ = Placed.rhs₇), and r7at a b c d, rule (7) with
-- its wires 0, 1, 2, 3 on the wires a, b, c, d.  A derivation is
-- checked by running it (run, a boolean computation on lists), and
-- run-sound turns a successful run into a derivation.  Lists are in
-- diagram order, the head first.  Open this module or Kit, not both:
-- their steps and equations have the same names.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.PlacedEngine where

open import Data.Bool.Base using (Bool ; true ; false ; T ; if_then_else_ ; _∧_ ; _∨_)
open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop ; map)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; _+_ ; _*_ ; _<ᵇ_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.Tactics.Words using (commutes ; module Commuting ; module Associative)
open Associative using (word-of-list)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (eqF ; eqF-sound)
open import Examples.Groups.XCXCCX-4bit.Placed
open import Examples.Groups.XCXCCX-4bit.Narrow3 using (narrowᵖ)

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

private
  ∧ˡ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧ʳ {true} h = h

  ∨-cases : ∀ a {b} → a ∨ b ≡ true → (a ≡ true) ⊎ (b ≡ true)
  ∨-cases true  _ = inj₁ Eq.refl
  ∨-cases false h = inj₂ h

  ≡→T : ∀ {b} → b ≡ true → T b
  ≡→T Eq.refl = tt

------------------------------------------------------------------------
-- Equality and order of letters

eqPG : PG → PG → Bool
eqPG (Xᵖ t)       (Xᵖ t′)         = t == t′
eqPG (CXᵖ c t)    (CXᵖ c′ t′)     = (c == c′) ∧ (t == t′)
eqPG (CCXᵖ a b t) (CCXᵖ a′ b′ t′) = (a == a′) ∧ ((b == b′) ∧ (t == t′))
eqPG _            _               = false

private
  cx≡ : ∀ {c c′ t t′} .{ok : T (okCX c t)} .{ok′ : T (okCX c′ t′)} →
        c ≡ c′ → t ≡ t′ → CXᵖ c t {ok} ≡ CXᵖ c′ t′ {ok′}
  cx≡ Eq.refl Eq.refl = Eq.refl

  ccx≡ : ∀ {a a′ b b′ t t′} .{ok : T (okCCX a b t)} .{ok′ : T (okCCX a′ b′ t′)} →
         a ≡ a′ → b ≡ b′ → t ≡ t′ → CCXᵖ a b t {ok} ≡ CCXᵖ a′ b′ t′ {ok′}
  ccx≡ Eq.refl Eq.refl Eq.refl = Eq.refl

eqPG-sound : (g h : PG) → eqPG g h ≡ true → g ≡ h
eqPG-sound (Xᵖ t) (Xᵖ t′) e = Eq.cong Xᵖ (==-sound t t′ (≡→T e))
eqPG-sound (CXᵖ c t {ok}) (CXᵖ c′ t′ {ok′}) e =
  cx≡ {ok = ok} {ok′ = ok′} (==-sound c c′ (≡→T (∧ˡ e))) (==-sound t t′ (≡→T (∧ʳ {c == c′} e)))
eqPG-sound (CCXᵖ a b t {ok}) (CCXᵖ a′ b′ t′ {ok′}) e =
  ccx≡ {ok = ok} {ok′ = ok′} (==-sound a a′ (≡→T (∧ˡ e)))
       (==-sound b b′ (≡→T (∧ˡ (∧ʳ {a == a′} e))))
       (==-sound t t′ (≡→T (∧ʳ {b == b′} (∧ʳ {a == a′} e))))
eqPG-sound (Xᵖ _)       (CXᵖ _ _)    ()
eqPG-sound (Xᵖ _)       (CCXᵖ _ _ _) ()
eqPG-sound (CXᵖ _ _)    (Xᵖ _)       ()
eqPG-sound (CXᵖ _ _)    (CCXᵖ _ _ _) ()
eqPG-sound (CCXᵖ _ _ _) (Xᵖ _)       ()
eqPG-sound (CCXᵖ _ _ _) (CXᵖ _ _)    ()

eqL : List PG → List PG → Bool
eqL []       []       = true
eqL (x ∷ xs) (y ∷ ys) = eqPG x y ∧ eqL xs ys
eqL _        _        = false

eqL-sound : (xs ys : List PG) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       _ = Eq.refl
eqL-sound (x ∷ xs) (y ∷ ys) e =
  Eq.cong₂ _∷_ (eqPG-sound x y (∧ˡ e)) (eqL-sound xs ys (∧ʳ {eqPG x y} e))
eqL-sound []       (_ ∷ _)  ()
eqL-sound (_ ∷ _)  []       ()

-- The order of the canonical forms: by a code of the letters.
code : PG → ℕ
code (Xᵖ t)       = toℕ t
code (CXᵖ c t)    = 4 + (4 * toℕ c + toℕ t)
code (CCXᵖ a b t) = 20 + (16 * toℕ a + (4 * toℕ b + toℕ t))

less : PG → PG → Bool
less g h = code g <ᵇ code h

------------------------------------------------------------------------
-- Commutation

-- The theory read back on words of letters: two words are related when
-- their circuits are.
Γᵖ : WRel PG
Γᵖ u v = 4 ⊢ ιʷ u ≈ ιʷ v

back : {u v : Word PG} → PB._≈_ Γᵖ u v → 4 ⊢ ιʷ u ≈ ιʷ v
back PB.refl         = refl
back (PB.sym p)      = sym (back p)
back (PB.trans p q)  = trans (back p) (back q)
back (PB.cong p q)   = cong (back p) (back q)
back PB.assoc        = assoc
back PB.left-unit    = left-unit
back PB.right-unit   = right-unit
back (PB.axiom a)    = a

-- Letters on disjoint wires commute.
comm? : (x y : PG) → Maybe (commutes Γᵖ x y)
comm? x y with disjoint x y in e
... | true  = just (PB.axiom (disj-comm x y e))
... | false = nothing

module Canon = Commuting PG Γᵖ comm? less
open Canon using (comm-canonical ; lemma-comm-canonical)

------------------------------------------------------------------------
-- Equations

record Eqnᵖ : Set where
  constructor eqnᵖ
  field
    lhs⁼ rhs⁼ : List PG
    prf       : 4 ⊢ ι* lhs⁼ ≈ ι* rhs⁼

open Eqnᵖ public

sym⁼ : Eqnᵖ → Eqnᵖ
sym⁼ (eqnᵖ l r p) = eqnᵖ r l (sym p)

-- An equation on other wires.
relabel⁼ : Relabel → Eqnᵖ → Eqnᵖ
relabel⁼ R (eqnᵖ l r p) = eqnᵖ (map (relabel R) l) (map (relabel R) r) (relabel-≈ R {l} {r} p)

-- Rule (7): CCX_{3,2→1} CX_{1→0} CCX_{3,2→1} = CCX_{3,2→0} CX_{1→0}.
r7⁼ : Eqnᵖ
r7⁼ = eqnᵖ lhs₇ rhs₇ rule7₀

-- Rule (7) with its wires 0, 1, 2, 3 on a, b, c, d.
r7at : (a b c d : Wire) → .{_ : T (distinct4 a b c d)} → Eqnᵖ
r7at a b c d {p} = relabel⁼ (ρ4 a b c d {p}) r7⁼

------------------------------------------------------------------------
-- Running a derivation

data Step : Set where
  perm   : List PG → Step
  rw     : ℕ → Eqnᵖ → Step
  narrow : ℕ → ℕ → List PG → Step

rewrite-at : ℕ → Eqnᵖ → List PG → List PG
rewrite-at i e xs = take i xs ++ (rhs⁼ e ++ drop (length (lhs⁼ e)) (drop i xs))

matches-at : ℕ → Eqnᵖ → List PG → Bool
matches-at i e xs = eqL (take (length (lhs⁼ e)) (drop i xs)) (lhs⁼ e)

narrow-at : ℕ → ℕ → List PG → List PG → List PG
narrow-at i k ys xs = take i xs ++ (ys ++ drop k (drop i xs))

-- u and v leave wire m alone and have the same function.
checkAt : Wire → List PG → List PG → Bool
checkAt m u v = (every (avoids m) u ∧ every (avoids m) v) ∧ eqF 4 ⟦ u ⟧ᵖ* ⟦ v ⟧ᵖ*

narrow-check : List PG → List PG → Bool
narrow-check u v = checkAt ₃ u v ∨ (checkAt ₂ u v ∨ (checkAt ₁ u v ∨ checkAt ₀ u v))

run : List Step → List PG → Maybe (List PG)
run []                   xs = just xs
run (perm ys ∷ ss)       xs =
  if eqL (comm-canonical xs) (comm-canonical ys) then run ss ys else nothing
run (rw i e ∷ ss)        xs =
  if matches-at i e xs then run ss (rewrite-at i e xs) else nothing
run (narrow i k ys ∷ ss) xs =
  if narrow-check (take k (drop i xs)) ys then run ss (narrow-at i k ys xs) else nothing

------------------------------------------------------------------------
-- Soundness

private
  ≡→≈ : {u v : Word PG} → u ≡ v → PB._≈_ Γᵖ u v
  ≡→≈ Eq.refl = PB.refl

  ι*-≡ : {xs ys : List PG} → xs ≡ ys → 4 ⊢ ι* xs ≈ ι* ys
  ι*-≡ Eq.refl = refl

  ι*-++ : (xs ys : List PG) → 4 ⊢ ι* (xs ++ ys) ≈ ι* xs • ι* ys
  ι*-++ []       ys = sym left-unit
  ι*-++ (x ∷ xs) ys = trans (cong refl (ι*-++ xs ys)) (sym assoc)

  -- Replacing the k letters at position i.
  splice : (i k : ℕ) (xs ys : List PG) → 4 ⊢ ι* (take k (drop i xs)) ≈ ι* ys →
           4 ⊢ ι* xs ≈ ι* (take i xs ++ (ys ++ drop k (drop i xs)))
  splice i k xs ys p = begin
    ι* xs                                                 ≈⟨ ι*-≡ (Eq.sym (take++drop≡id i xs)) ⟩
    ι* (take i xs ++ drop i xs)                           ≈⟨ ι*-++ (take i xs) (drop i xs) ⟩
    ι* (take i xs) • ι* (drop i xs)                       ≈⟨ cong refl (ι*-≡ (Eq.sym (take++drop≡id k (drop i xs)))) ⟩
    ι* (take i xs) • ι* (take k (drop i xs) ++ rest)      ≈⟨ cong refl (ι*-++ (take k (drop i xs)) rest) ⟩
    ι* (take i xs) • (ι* (take k (drop i xs)) • ι* rest)  ≈⟨ cong refl (cong p refl) ⟩
    ι* (take i xs) • (ι* ys • ι* rest)                    ≈⟨ cong refl (sym (ι*-++ ys rest)) ⟩
    ι* (take i xs) • ι* (ys ++ rest)                      ≈⟨ sym (ι*-++ (take i xs) (ys ++ rest)) ⟩
    ι* (take i xs ++ (ys ++ rest))                        ∎
    where
    open SR (PP.word-setoid (4 VRel,_===_))
    rest = drop k (drop i xs)

  checkAt-sound : (m : Wire) (u v : List PG) → checkAt m u v ≡ true → 4 ⊢ ι* u ≈ ι* v
  checkAt-sound m u v h =
    narrowᵖ m u v (∧ˡ hm) (∧ʳ {every (avoids m) u} hm)
      (eqF-sound 4 ⟦ u ⟧ᵖ* ⟦ v ⟧ᵖ* (∧ʳ {every (avoids m) u ∧ every (avoids m) v} h))
    where
    hm = ∧ˡ {every (avoids m) u ∧ every (avoids m) v} h

perm-sound : (xs ys : List PG) → comm-canonical xs ≡ comm-canonical ys → 4 ⊢ ι* xs ≈ ι* ys
perm-sound xs ys e = back (PB.trans (lemma-comm-canonical xs)
  (PB.trans (≡→≈ (Eq.cong word-of-list e)) (PB.sym (lemma-comm-canonical ys))))

rw-sound : (i : ℕ) (e : Eqnᵖ) (xs : List PG) → matches-at i e xs ≡ true → 4 ⊢ ι* xs ≈ ι* (rewrite-at i e xs)
rw-sound i e xs h =
  splice i (length (lhs⁼ e)) xs (rhs⁼ e) (trans (ι*-≡ {blk} {lhs⁼ e} (eqL-sound blk (lhs⁼ e) h)) (prf e))
  where blk = take (length (lhs⁼ e)) (drop i xs)

narrow-sound : (u v : List PG) → narrow-check u v ≡ true → 4 ⊢ ι* u ≈ ι* v
narrow-sound u v h =
  [ checkAt-sound ₃ u v
  , (λ h₂ → [ checkAt-sound ₂ u v
            , (λ h₁ → [ checkAt-sound ₁ u v , checkAt-sound ₀ u v ]′ (∨-cases (checkAt ₁ u v) h₁))
            ]′ (∨-cases (checkAt ₂ u v) h₂))
  ]′ (∨-cases (checkAt ₃ u v) h)

run-sound : (ss : List Step) (xs ys : List PG) → run ss xs ≡ just ys → 4 ⊢ ι* xs ≈ ι* ys
run-sound []             xs ys Eq.refl = refl
run-sound (perm zs ∷ ss) xs ys h with eqL (comm-canonical xs) (comm-canonical zs) in c
run-sound (perm zs ∷ ss) xs ys h  | true  =
  trans (perm-sound xs zs (eqL-sound _ _ c)) (run-sound ss zs ys h)
run-sound (perm zs ∷ ss) xs ys () | false
run-sound (rw i e ∷ ss)  xs ys h with matches-at i e xs in c
run-sound (rw i e ∷ ss)  xs ys h  | true  =
  trans (rw-sound i e xs c) (run-sound ss (rewrite-at i e xs) ys h)
run-sound (rw i e ∷ ss)  xs ys () | false
run-sound (narrow i k zs ∷ ss) xs ys h with narrow-check (take k (drop i xs)) zs in c
run-sound (narrow i k zs ∷ ss) xs ys h  | true  =
  trans (splice i k xs zs (narrow-sound (take k (drop i xs)) zs c)) (run-sound ss (narrow-at i k zs xs) ys h)
run-sound (narrow i k zs ∷ ss) xs ys () | false

-- A derivation: an equation from the steps that turn l into r.
derive : (l r : List PG) (ss : List Step) → run ss l ≡ just r → Eqnᵖ
derive l r ss h = eqnᵖ l r (run-sound ss l r h)

------------------------------------------------------------------------
-- Tests

private
  -- X on wire 0 passes the Toffoli on the wires above it (perm), two of
  -- them cancel (narrow, on the wires 0 1 2), and rule (7) applies (rw).
  test₁ : Eqnᵖ
  test₁ = derive (Xᵖ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₀ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ [])
    (CCXᵖ ₂ ₃ ₀ ∷ CXᵖ ₁ ₀ ∷ [])
    (perm (CCXᵖ ₂ ₃ ₁ ∷ Xᵖ ₀ ∷ Xᵖ ₀ ∷ CXᵖ ₁ ₀ ∷ CCXᵖ ₂ ₃ ₁ ∷ []) ∷
     narrow 1 2 [] ∷
     rw 0 (r7at ₀ ₁ ₂ ₃) ∷ [])
    Eq.refl

  -- Rule (7) upside down, forwards and backwards, with narrow steps on
  -- the wires 1 2 3 and 0 2 3.
  test₂ : Eqnᵖ
  test₂ = derive (CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ [])
    (CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ [])
    (rw 0 (r7at ₃ ₂ ₁ ₀) ∷
     narrow 1 2 [] ∷
     narrow 1 0 (CXᵖ ₃ ₂ ∷ CXᵖ ₃ ₂ ∷ []) ∷ [])
    Eq.refl

  test₃ : Eqnᵖ
  test₃ = derive (CCXᵖ ₀ ₁ ₃ ∷ CXᵖ ₂ ₃ ∷ CXᵖ ₂ ₃ ∷ [])
    (CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ CCXᵖ ₀ ₁ ₂ ∷ CXᵖ ₂ ₃ ∷ [])
    (rw 0 (sym⁼ (r7at ₃ ₂ ₁ ₀)) ∷ [])
    Eq.refl

  -- Two CNOTs on disjoint pairs of wires commute, and CCX_{3,2→0} is an
  -- involution.
  test₄ : Eqnᵖ
  test₄ = derive (CXᵖ ₁ ₀ ∷ CXᵖ ₃ ₂ ∷ CCXᵖ ₂ ₃ ₀ ∷ CCXᵖ ₂ ₃ ₀ ∷ [])
    (CXᵖ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ [])
    (narrow 2 2 [] ∷
     perm (CXᵖ ₃ ₂ ∷ CXᵖ ₁ ₀ ∷ []) ∷ [])
    Eq.refl
