------------------------------------------------------------------------
-- Presentations of groups
--
-- Certificates over words of labels
--
-- Labels stand for involutions of a group (here perfect matchings of
-- eight states), interpreted as words X x of some theory.  Given that
-- each X x is an involution (inv), that X x conjugates X y to the
-- label of x y x (conj, under a decided side condition cok), and that
-- two labels whose product is a label (side condition kok, decided)
-- multiply to it (klein), a word of labels can be rewritten by moves
-- whose side conditions are decided on the labels alone:
--
--   H i     x y   ↦  (x y x) x          Hi i    x y   ↦  y (y x y)
--   C i     x x   ↦  ε                  I i z   ε     ↦  z z
--   K i     x y   ↦  (x y)              Ki i x y  z   ↦  x y  (x y = z)
--
-- run checks a certificate (a list of moves) as a boolean computation,
-- and run-sound turns a successful run into a derivation between the
-- interpretations of the two words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB

module Examples.Groups.XCXCCX-4bit.LabelEngine
  {L : Set}
  (_≟ᴸ_ : L → L → Bool)
  (c3 : L → L → L) (cok : L → L → Bool) (mul : L → L → L) (kok : L → L → Bool)
  where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_)


private
  ∧ˡ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧ʳ {true} h = h

------------------------------------------------------------------------
-- Moves and their runs

data Move : Set where
  H  : ℕ → Move
  Hi : ℕ → Move
  C  : ℕ → Move
  I  : ℕ → L → Move
  K  : ℕ → Move
  Ki : ℕ → L → L → Move

-- A move applied at the head of a word (after the first i letters are
-- skipped by step).
local : Move → List L → Maybe (List L)
local (H _)  (x ∷ y ∷ r) = if cok x y then just (c3 x y ∷ x ∷ r) else nothing
local (Hi _) (x ∷ y ∷ r) = if cok y x then just (y ∷ c3 y x ∷ r) else nothing
local (C _)  (x ∷ y ∷ r) = if x ≟ᴸ y then just r else nothing
local (I _ z) r          = just (z ∷ z ∷ r)
local (K _)  (x ∷ y ∷ r) = if kok x y then just (mul x y ∷ r) else nothing
local (Ki _ x y) (z ∷ r) = if kok x y ∧ (mul x y ≟ᴸ z) then just (x ∷ y ∷ r) else nothing
local _      _           = nothing

index : Move → ℕ
index (H i)      = i
index (Hi i)     = i
index (C i)      = i
index (I i _)    = i
index (K i)      = i
index (Ki i _ _) = i

-- Apply a move at position i.
at : ℕ → Move → List L → Maybe (List L)
at zero    m xs       = local m xs
at (suc i) m []       = nothing
at (suc i) m (x ∷ xs) with at i m xs
... | just ys = just (x ∷ ys)
... | nothing = nothing

step : Move → List L → Maybe (List L)
step m = at (index m) m

eqL : List L → List L → Bool
eqL []       []       = true
eqL (x ∷ xs) (y ∷ ys) = (x ≟ᴸ y) ∧ eqL xs ys
eqL _        _        = false

run : List Move → List L → Maybe (List L)
run []       xs = just xs
run (m ∷ ms) xs with step m xs
... | just ys = run ms ys
... | nothing = nothing

-- A certificate: the run from l ends in r.
check : List Move → List L → List L → Bool
check ms l r with run ms l
... | just r′ = eqL r′ r
... | nothing = false

------------------------------------------------------------------------
-- Soundness, for an interpretation satisfying the relations

module Sound
  {A : Set} (Γ : WRel A) (X : L → Word A)
  (≟ᴸ-sound : ∀ x y → (x ≟ᴸ y) ≡ true → x ≡ y)
  (inv   : ∀ x → PB._≈_ Γ (X x • X x) ε)
  (conj  : ∀ x y → cok x y ≡ true → PB._≈_ Γ (X x • X y • X x) (X (c3 x y)))
  (klein : ∀ x y → kok x y ≡ true → PB._≈_ Γ (X x • X y) (X (mul x y)))
  where

  open PB Γ using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  eqL-sound : (xs ys : List L) → eqL xs ys ≡ true → xs ≡ ys
  eqL-sound []       []       _ = Eq.refl
  eqL-sound (x ∷ xs) (y ∷ ys) h =
    Eq.cong₂ _∷_ (≟ᴸ-sound x y (∧ˡ h)) (eqL-sound xs ys (∧ʳ {x ≟ᴸ y} h))
  eqL-sound []       (_ ∷ _)  ()
  eqL-sound (_ ∷ _)  []       ()


  ------------------------------------------------------------------------
  -- Words of labels

  Xs : List L → Word A
  Xs []       = ε
  Xs (x ∷ xs) = X x • Xs xs

  Xs-++ : (xs ys : List L) → Xs (xs ++ ys) ≈ Xs xs • Xs ys
  Xs-++ []       ys = sym left-unit
  Xs-++ (x ∷ xs) ys = trans (cong refl (Xs-++ xs ys)) (sym assoc)

  ------------------------------------------------------------------------
  -- The local moves

  -- X x X y = X (x y x) X x.
  h-move : ∀ x y → cok x y ≡ true → X x • X y ≈ X (c3 x y) • X x
  h-move x y c =
    trans (sym right-unit)
    (trans (cong refl (sym (inv x)))
    (trans (sym assoc) (cong (trans assoc (conj x y c)) refl)))

  -- X x X y = X y X (y x y).
  hi-move : ∀ x y → cok y x ≡ true → X x • X y ≈ X y • X (c3 y x)
  hi-move x y c =
    trans (sym left-unit)
    (trans (cong (sym (inv y)) refl)
    (trans assoc (cong refl (conj y x c))))


  ------------------------------------------------------------------------
  -- Soundness

  private
    ≡→≈ : {u v : Word A} → u ≡ v → u ≈ v
    ≡→≈ Eq.refl = refl

    if-just : ∀ (b : Bool) {r : List L} {ys : List L} → (if b then just r else nothing) ≡ just ys → (b ≡ true) × (r ≡ ys)
    if-just true  Eq.refl = Eq.refl , Eq.refl
    if-just false ()

  local-sound : (m : Move) (xs ys : List L) → local m xs ≡ just ys → Xs xs ≈ Xs ys
  local-sound (H _)  (x ∷ y ∷ r) ys e with if-just (cok x y) e
  ... | b , Eq.refl = trans (sym assoc) (trans (cong (h-move x y b) refl) assoc)
  local-sound (Hi _) (x ∷ y ∷ r) ys e with if-just (cok y x) e
  ... | b , Eq.refl = trans (sym assoc) (trans (cong (hi-move x y b) refl) assoc)
  local-sound (C _)  (x ∷ y ∷ r) ys e with if-just (x ≟ᴸ y) e
  ... | b , Eq.refl with ≟ᴸ-sound x y b
  ... | Eq.refl = trans (sym assoc) (trans (cong (inv x) refl) left-unit)
  local-sound (I _ z) r _ Eq.refl = sym (trans (sym assoc) (trans (cong (inv z) refl) left-unit))
  local-sound (K _)  (x ∷ y ∷ r) ys e with if-just (kok x y) e
  ... | b , Eq.refl = trans (sym assoc) (cong (klein x y b) refl)
  local-sound (Ki _ x y) (z ∷ r) ys e with if-just (kok x y ∧ (mul x y ≟ᴸ z)) e
  ... | b , Eq.refl with ≟ᴸ-sound (mul x y) z (∧ʳ {kok x y} b)
  ... | Eq.refl = sym (trans (sym assoc) (cong (klein x y (∧ˡ b)) refl))
  local-sound (H _)  []          _ ()
  local-sound (H _)  (_ ∷ [])    _ ()
  local-sound (Hi _) []          _ ()
  local-sound (Hi _) (_ ∷ [])    _ ()
  local-sound (C _)  []          _ ()
  local-sound (C _)  (_ ∷ [])    _ ()
  local-sound (K _)  []          _ ()
  local-sound (K _)  (_ ∷ [])    _ ()
  local-sound (Ki _ _ _) []      _ ()

  at-sound : (i : ℕ) (m : Move) (xs ys : List L) → at i m xs ≡ just ys → Xs xs ≈ Xs ys
  at-sound zero    m xs       ys e = local-sound m xs ys e
  at-sound (suc i) m []       ys ()
  at-sound (suc i) m (x ∷ xs) ys e with at i m xs in a
  at-sound (suc i) m (x ∷ xs) ys Eq.refl | just zs = cong refl (at-sound i m xs zs a)
  at-sound (suc i) m (x ∷ xs) ys ()      | nothing

  run-sound : (ms : List Move) (xs ys : List L) → run ms xs ≡ just ys → Xs xs ≈ Xs ys
  run-sound []       xs ys Eq.refl = refl
  run-sound (m ∷ ms) xs ys e with step m xs in s
  ... | just zs = trans (at-sound (index m) m xs zs s) (run-sound ms zs ys e)
  run-sound (m ∷ ms) xs ys () | nothing

  -- A checked certificate is a derivation.
  check-sound : (ms : List Move) (l r : List L) → check ms l r ≡ true → Xs l ≈ Xs r
  check-sound ms l r h with run ms l in e
  ... | just r′ = Eq.subst (λ z → Xs l ≈ Xs z) (eqL-sound r′ r h) (run-sound ms l r′ e)
  check-sound ms l r () | nothing
