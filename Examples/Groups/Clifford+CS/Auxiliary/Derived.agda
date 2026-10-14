------------------------------------------------------------------------
-- Presentations of groups
--
-- Derived equations of the K-free fragment
--
-- What `NF` needs beyond the axioms: the phase-pair inverse and the
-- order-four consequences, and the full conjugation theory — a letter
-- on a consecutive pair carries any phase pair to a phase pair, the
-- indices transposed (`conj-any`, the analogue of Clément's Figure 9
-- conjugations (58)–(62)).  The two axioms `px-conj` and `px-conj₂`
-- generate every configuration: an inverse pair crosses by cancelling
-- (`inv-pass`), and the remaining shapes split through a pair index by
-- the telescope, so no fresh index is ever needed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.Derived (N : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (suc ; _<_ ; _≤_ ; zero)
open import Data.Nat.Properties using (n≮n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _^_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment

open PB (N F,_===_) public
  using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
open import Presentation.Properties (N F,_===_) public
  using (word-setoid ; ^-suc ; ^-+ ; pow-comm ; comm⇒pow-comm ; ^-• ; ^^ ;
         ^-cong ; ε^k=ε ; by-assoc)
open SR word-setoid public

private
  W : Set
  W = Word (GenP N)

------------------------------------------------------------------------
-- The kit

front : ∀ {a b} (s : W) → a ≈ b → a • s ≈ b • s
front s e = cong e refl

back : ∀ (p : W) {a b} → a ≈ b → p • a ≈ p • b
back p e = cong refl e

-- Cancelling an inverse pair at either end.
cancelˡ⁻ : ∀ {c c′} (s : W) → c • c′ ≈ ε → c • (c′ • s) ≈ s
cancelˡ⁻ s e = trans (sym assoc) (trans (front s e) left-unit)

cancelʳ⁻ : ∀ (p : W) {c c′} → c • c′ ≈ ε → (p • c) • c′ ≈ p
cancelʳ⁻ p e = trans assoc (trans (back p e) right-unit)

-- An inverse pair crosses an equation: from X • p ≈ q • X, the
-- inverses cross the other way.
inv-pass : ∀ {x p q p′ q′ : W} → x • p ≈ q • x →
           p • p′ ≈ ε → q′ • q ≈ ε → x • p′ ≈ q′ • x
inv-pass {x} {p} {q} {p′} {q′} E ip iq = begin
  x • p′                 ≈⟨ sym left-unit ⟩
  ε • (x • p′)           ≈⟨ front (x • p′) (sym iq) ⟩
  (q′ • q) • (x • p′)    ≈⟨ assoc ⟩
  q′ • (q • (x • p′))    ≈⟨ back q′ (sym assoc) ⟩
  q′ • ((q • x) • p′)    ≈⟨ back q′ (front p′ (sym E)) ⟩
  q′ • ((x • p) • p′)    ≈⟨ back q′ assoc ⟩
  q′ • (x • (p • p′))    ≈⟨ back q′ (back x ip) ⟩
  q′ • (x • ε)           ≈⟨ back q′ right-unit ⟩
  q′ • x ∎

-- An equation crosses a power.
pass-pow : ∀ {x p q : W} → x • p ≈ q • x → ∀ k → x • p ^ k ≈ q ^ k • x
pass-pow {x} {p} {q} E zero = trans right-unit (sym left-unit)
pass-pow {x} {p} {q} E (suc zero) = E
pass-pow {x} {p} {q} E (suc (suc k)) = begin
  x • (p • p ^ suc k)        ≈⟨ sym assoc ⟩
  (x • p) • p ^ suc k        ≈⟨ front _ E ⟩
  (q • x) • p ^ suc k        ≈⟨ assoc ⟩
  q • (x • p ^ suc k)        ≈⟨ back q (pass-pow E (suc k)) ⟩
  q • (q ^ suc k • x)        ≈⟨ sym assoc ⟩
  (q • q ^ suc k) • x ∎

------------------------------------------------------------------------
-- The phase-pair algebra

-- A pair and its reverse cancel.
pp-inv : ∀ (a b : Fin N) → pw a b • pw b a ≈ ε
pp-inv a b = trans (axiom (pp-tele a b a)) (axiom (pp-id a))

-- The reverse squared is the pair squared (order four).
pp-swap² : ∀ (a b : Fin N) → pw b a • pw b a ≈ pw a b • pw a b
pp-swap² a b = begin
  Y • Y                          ≈⟨ sym right-unit ⟩
  (Y • Y) • ε                    ≈⟨ back (Y • Y) (sym (axiom (pp-ord a b))) ⟩
  (Y • Y) • (X • (X • (X • X)))  ≈⟨ assoc ⟩
  Y • (Y • (X • (X • (X • X))))  ≈⟨ back Y (cancelˡ⁻ (X • (X • X)) (pp-inv b a)) ⟩
  Y • (X • (X • X))              ≈⟨ cancelˡ⁻ (X • X) (pp-inv b a) ⟩
  X • X ∎
  where
  X = pw a b
  Y = pw b a

------------------------------------------------------------------------
-- The letter on a consecutive pair

-- Abbreviation: the letter with its phase on the lower index.
sxF : ∀ (a a′ : Fin N) (s : Succ a a′) → W
sxF a a′ s = xw a a a′ (s< s)

private
  Succ≢ : ∀ {a a′ : Fin N} → Succ a a′ → a ≢ a′
  Succ≢ {a} {a′} s e =
    n≮n (toℕ a) (Eq.subst (suc (toℕ a) ≤_) (Eq.cong toℕ (Eq.sym e)) (s< s))

------------------------------------------------------------------------
-- The conjugation steps
--
-- Everything is leftward: the letter moves right past a phase pair,
-- which comes out with its indices transposed.

module _ (a a′ : Fin N) (s : Succ a a′) where

  private
    sx′ : W
    sx′ = sxF a a′ s

  -- The two axioms, read leftward.
  cA : ∀ (c : Fin N) → c ≢ a → c ≢ a′ → sx′ • pw a c ≈ pw a′ c • sx′
  cA c ca ca′ = sym (axiom (px-conj a a′ c s ca ca′))

  cC′ : sx′ • pw a′ a ≈ pw a a′ • sx′
  cC′ = sym (axiom (px-conj₂ a a′ s))

  -- Their inverses.
  cB : ∀ (c : Fin N) → c ≢ a → c ≢ a′ → sx′ • pw c a ≈ pw c a′ • sx′
  cB c ca ca′ = inv-pass (cA c ca ca′) (pp-inv a c) (pp-inv c a′)

  cC : sx′ • pw a a′ ≈ pw a′ a • sx′
  cC = inv-pass cC′ (pp-inv a′ a) (pp-inv a′ a)

  -- The remaining shapes, by telescoping through a pair index.
  cA′ : ∀ (c : Fin N) → c ≢ a → c ≢ a′ → sx′ • pw a′ c ≈ pw a c • sx′
  cA′ c ca ca′ = begin
    sx′ • pw a′ c                ≈⟨ back sx′ (sym (axiom (pp-tele a′ a c))) ⟩
    sx′ • (pw a′ a • pw a c)     ≈⟨ sym assoc ⟩
    (sx′ • pw a′ a) • pw a c     ≈⟨ front _ cC′ ⟩
    (pw a a′ • sx′) • pw a c     ≈⟨ assoc ⟩
    pw a a′ • (sx′ • pw a c)     ≈⟨ back _ (cA c ca ca′) ⟩
    pw a a′ • (pw a′ c • sx′)    ≈⟨ sym assoc ⟩
    (pw a a′ • pw a′ c) • sx′    ≈⟨ front sx′ (axiom (pp-tele a a′ c)) ⟩
    pw a c • sx′ ∎

  cB′ : ∀ (c : Fin N) → c ≢ a → c ≢ a′ → sx′ • pw c a′ ≈ pw c a • sx′
  cB′ c ca ca′ = begin
    sx′ • pw c a′                ≈⟨ back sx′ (sym (axiom (pp-tele c a a′))) ⟩
    sx′ • (pw c a • pw a a′)     ≈⟨ sym assoc ⟩
    (sx′ • pw c a) • pw a a′     ≈⟨ front _ (cB c ca ca′) ⟩
    (pw c a′ • sx′) • pw a a′    ≈⟨ assoc ⟩
    pw c a′ • (sx′ • pw a a′)    ≈⟨ back _ cC ⟩
    pw c a′ • (pw a′ a • sx′)    ≈⟨ sym assoc ⟩
    (pw c a′ • pw a′ a) • sx′    ≈⟨ front sx′ (axiom (pp-tele c a′ a)) ⟩
    pw c a • sx′ ∎

  cD : ∀ (x y : Fin N) → x ≢ a → x ≢ a′ → y ≢ a → y ≢ a′ →
       sx′ • pw x y ≈ pw x y • sx′
  cD x y xa xa′ ya ya′ = begin
    sx′ • pw x y                 ≈⟨ back sx′ (sym (axiom (pp-tele x a y))) ⟩
    sx′ • (pw x a • pw a y)      ≈⟨ sym assoc ⟩
    (sx′ • pw x a) • pw a y      ≈⟨ front _ (cB x xa xa′) ⟩
    (pw x a′ • sx′) • pw a y     ≈⟨ assoc ⟩
    pw x a′ • (sx′ • pw a y)     ≈⟨ back _ (cA y ya ya′) ⟩
    pw x a′ • (pw a′ y • sx′)    ≈⟨ sym assoc ⟩
    (pw x a′ • pw a′ y) • sx′    ≈⟨ front sx′ (axiom (pp-tele x a′ y)) ⟩
    pw x y • sx′ ∎

  -- A degenerate pair is ε on both sides.
  cE : ∀ (x : Fin N) → sx′ • pw x x ≈ pw x x • sx′
  cE x = begin
    sx′ • pw x x    ≈⟨ back sx′ (axiom (pp-id x)) ⟩
    sx′ • ε         ≈⟨ right-unit ⟩
    sx′             ≈⟨ sym left-unit ⟩
    ε • sx′         ≈⟨ front sx′ (sym (axiom (pp-id x))) ⟩
    pw x x • sx′ ∎

------------------------------------------------------------------------
-- Any phase pair crosses the letter

record Conj (a a′ : Fin N) (s : Succ a a′) (x y : Fin N) : Set where
  constructor conj
  field
    cx cy : Fin N
    law   : sxF a a′ s • pw x y ≈ pw cx cy • sxF a a′ s

conj-any : ∀ (a a′ : Fin N) (s : Succ a a′) (x y : Fin N) →
           Conj a a′ s x y
conj-any a a′ s x y = go (x ≟ y) (x ≟ a) (x ≟ a′) (y ≟ a) (y ≟ a′)
  where
  aa′ = Succ≢ s

  go : Dec (x ≡ y) → Dec (x ≡ a) → Dec (x ≡ a′) → Dec (y ≡ a) → Dec (y ≡ a′) →
       Conj a a′ s x y
  go (yes Eq.refl) _ _ _ _ = conj x x (cE a a′ s x)
  go (no xy) (yes Eq.refl) _ (yes e) _ = ⊥-elim (xy (Eq.sym e))
  go (no xy) (yes Eq.refl) _ (no ya) (yes Eq.refl) = conj a′ a (cC a a′ s)
  go (no xy) (yes Eq.refl) _ (no ya) (no ya′) =
    conj a′ y (cA a a′ s y (λ e → ya e) ya′)
  go (no xy) (no xa) (yes Eq.refl) (yes Eq.refl) _ = conj a a′ (cC′ a a′ s)
  go (no xy) (no xa) (yes Eq.refl) (no ya) (yes e) = ⊥-elim (xy (Eq.sym e))
  go (no xy) (no xa) (yes Eq.refl) (no ya) (no ya′) =
    conj a y (cA′ a a′ s y ya ya′)
  go (no xy) (no xa) (no xa′) (yes Eq.refl) _ = conj x a′ (cB a a′ s x xa xa′)
  go (no xy) (no xa) (no xa′) (no ya) (yes Eq.refl) =
    conj x a (cB′ a a′ s x xa xa′)
  go (no xy) (no xa) (no xa′) (no ya) (no ya′) =
    conj x y (cD a a′ s x y xa xa′ ya ya′)

-- And so does any power of one.
conj-pow : ∀ (a a′ : Fin N) (s : Succ a a′) (x y : Fin N) (k : ℕ) →
           sxF a a′ s • pw x y ^ k
           ≈ pw (Conj.cx (conj-any a a′ s x y)) (Conj.cy (conj-any a a′ s x y)) ^ k
             • sxF a a′ s
conj-pow a a′ s x y k = pass-pow (Conj.law (conj-any a a′ s x y)) k
