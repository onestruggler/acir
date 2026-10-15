------------------------------------------------------------------------
-- Presentations of groups
--
-- Coxeter words that send the first basis states to given ones.
--
-- cyc t sends 0 to t and every other state x to the one below it
-- (punchIn t); frame ts, for a list ts of distinct states, sends the
-- state i to the i-th entry of ts (frame-act): it is cyc of the head,
-- followed, one wire up, by the frame of the rest punched out at the
-- head.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Frame where

open import Data.Fin.Base using (Fin ; zero ; suc ; punchIn ; punchOut ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as Sym
open Sym using (gate₂ ; σ-gate)

open import Examples.Groups.CCX+HH-3qubit-opus.Perm using (SG ; actₙ ; act-•)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The action of a word lifted one wire up

act-↑-0 : (w : Word (SG n)) → actₙ (w Sym.↑) zero ≡ zero
act-↑-0 [ g ]ʷ   = Eq.refl
act-↑-0 ε       = Eq.refl
act-↑-0 (u • v) = Eq.trans (Eq.cong (actₙ (u Sym.↑)) (act-↑-0 v)) (act-↑-0 u)

act-↑-suc : (w : Word (SG n)) (x : Fin n) → actₙ (w Sym.↑) (suc x) ≡ suc (actₙ w x)
act-↑-suc [ g ]ʷ   x = Eq.refl
act-↑-suc ε       x = Eq.refl
act-↑-suc (u • v) x = Eq.trans (Eq.cong (actₙ (u Sym.↑)) (act-↑-suc v x)) (act-↑-suc u (actₙ v x))

------------------------------------------------------------------------
-- Cycles

cyc : Fin (suc n) → Word (SG (suc n))
cyc {zero}  zero    = ε
cyc {suc n} zero    = ε
cyc {suc n} (suc t) = cyc t Sym.↑ • [ gate₂ σ-gate ]ʷ

cyc-0 : (t : Fin (suc n)) → actₙ (cyc t) zero ≡ t
cyc-0 {zero}  zero    = Eq.refl
cyc-0 {suc n} zero    = Eq.refl
cyc-0 {suc n} (suc t) = Eq.trans (act-↑-suc (cyc t) zero) (Eq.cong suc (cyc-0 t))

cyc-suc : (t : Fin (suc n)) (x : Fin n) → actₙ (cyc t) (suc x) ≡ punchIn t x
cyc-suc {suc n} zero    x       = Eq.refl
cyc-suc {suc n} (suc t) zero    = act-↑-0 (cyc t)
cyc-suc {suc n} (suc t) (suc x) = Eq.trans (act-↑-suc (cyc t) (suc x)) (Eq.cong suc (cyc-suc t x))

------------------------------------------------------------------------
-- Frames

-- A list of states, each different from the given one.
data Avoid {n : ℕ} (t : Fin n) : List (Fin n) → Set where
  []  : Avoid t []
  _∷_ : ∀ {x xs} → t ≢ x → Avoid t xs → Avoid t (x ∷ xs)

-- Distinct states.
data Distinct {n : ℕ} : List (Fin n) → Set where
  []  : Distinct []
  _∷_ : ∀ {x xs} → Avoid x xs → Distinct xs → Distinct (x ∷ xs)

-- The rest of a list, punched out at a state it avoids.
outs : (t : Fin (suc n)) (xs : List (Fin (suc n))) → Avoid t xs → List (Fin n)
outs t []       []       = []
outs t (x ∷ xs) (p ∷ a)  = punchOut p ∷ outs t xs a

private
  avoid-out : {t x : Fin (suc n)} (p : t ≢ x) (xs : List (Fin (suc n))) (a : Avoid t xs) →
              Avoid x xs → Avoid (punchOut p) (outs t xs a)
  avoid-out p []       []       []       = []
  avoid-out p (y ∷ ys) (q ∷ a)  (r ∷ b)  = (λ e → r (FinP.punchOut-injective p q e)) ∷ avoid-out p ys a b

  distinct-out : (t : Fin (suc n)) (xs : List (Fin (suc n))) (a : Avoid t xs) → Distinct xs → Distinct (outs t xs a)
  distinct-out t []       []       []       = []
  distinct-out t (x ∷ xs) (p ∷ a)  (b ∷ d)  = avoid-out p xs a b ∷ distinct-out t xs a d

frame : (ts : List (Fin n)) → Distinct ts → Word (SG n)
frame []                   []       = ε
frame {suc n} (t ∷ ts)     (a ∷ d)  = cyc t • frame (outs t ts a) (distinct-out t ts a d) Sym.↑

-- The i-th entry of a list.
_‼_ : {A : Set} → List A → ℕ → Maybe A
[]       ‼ i       = nothing
(x ∷ xs) ‼ zero    = just x
(x ∷ xs) ‼ (suc i) = xs ‼ i

private
  outs-‼ : (t : Fin (suc n)) (xs : List (Fin (suc n))) (a : Avoid t xs) (j : ℕ) {x : Fin (suc n)} →
           xs ‼ j ≡ just x → Σ (t ≢ x) λ p → outs t xs a ‼ j ≡ just (punchOut p)
  outs-‼ t (y ∷ ys) (p ∷ a) zero    Eq.refl = p , Eq.refl
  outs-‼ t (y ∷ ys) (p ∷ a) (suc j) h       = outs-‼ t ys a j h

-- frame ts sends i to the i-th entry of ts.
frame-act : (ts : List (Fin n)) (d : Distinct ts) (i x : Fin n) → ts ‼ toℕ i ≡ just x → actₙ (frame ts d) i ≡ x
frame-act {suc n} (t ∷ ts) (a ∷ d) zero x Eq.refl =
  Eq.trans (Eq.cong (actₙ (cyc t)) (act-↑-0 (frame (outs t ts a) (distinct-out t ts a d)))) (cyc-0 t)
frame-act {suc n} (t ∷ ts) (a ∷ d) (suc i) x h =
  Eq.trans (Eq.cong (actₙ (cyc t)) (act-↑-suc F i))
    (Eq.trans (cyc-suc t (actₙ F i))
      (Eq.trans (Eq.cong (punchIn t) (frame-act (outs t ts a) (distinct-out t ts a d) i (punchOut p) e))
        (FinP.punchIn-punchOut p)))
  where
  F = frame (outs t ts a) (distinct-out t ts a d)
  o = outs-‼ t ts a (toℕ i) h
  p = proj₁ o
  e = proj₂ o
