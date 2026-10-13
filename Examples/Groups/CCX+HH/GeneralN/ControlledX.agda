------------------------------------------------------------------------
-- Presentations of groups
--
-- A fixed-width compiler for multiply controlled X gates.  Its input
-- supplies one distinct borrowed wire, whose initial value is arbitrary.
-- The recursive construction restores that wire and all non-target
-- wires.  The output uses only X, CX and CCX at named wire positions.
-- Instantiating Wire with Fin n fixes the width; no wire is allocated.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Examples.Groups.CCX+HH.GeneralN.ControlledX
  (Wire : Set) (_≟_ : DecidableEquality Wire) where

open import Data.Bool.Base using (Bool ; true ; _∧_)
open import Data.Bool.Properties using (∧-identityʳ ; ∧-assoc)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Examples.Groups.CCX+HH.GeneralN.BorrowedBit as Borrowed
open Borrowed Wire _≟_ public using (State ; _≈s_ ; toggle)
private module B = Borrowed Wire _≟_

private variable k : ℕ

Fresh : Wire → Vec Wire k → Set
Fresh a [] = ⊤
Fresh a (b ∷ bs) = a ≢ b × Fresh a bs

Distinct : Vec Wire k → Set
Distinct [] = ⊤
Distinct (a ∷ as) = Fresh a as × Distinct as

record Valid (cs : Vec Wire k) (target spare : Wire) : Set where
  field
    target≢spare : target ≢ spare
    target-fresh : Fresh target cs
    spare-fresh : Fresh spare cs
    distinct : Distinct cs
open Valid

controls : Vec Wire k → State → Bool
controls [] s = true
controls (c ∷ cs) s = s c ∧ controls cs s

controlled : Vec Wire k → Wire → State → State
controlled cs t s = toggle t (controls cs s) s

data Gate : Set where
  X : Wire → Gate
  CX : Wire → Wire → Gate
  CCX : Wire → Wire → Wire → Gate

act₀ : Gate → State → State
act₀ (X t) = controlled [] t
act₀ (CX c t) = controlled (c ∷ []) t
act₀ (CCX a b t) = controlled (a ∷ b ∷ []) t

act : Word Gate → State → State
act [ g ]ʷ = act₀ g
act ε s = s
act (u • v) s = act u (act v s)

-- The controls' arity strictly decreases in the recursive call.
compile : (k : ℕ) → Vec Wire k → Wire → Wire → Word Gate
compile zero [] t r = [ X t ]ʷ
compile (suc zero) (a ∷ []) t r = [ CX a t ]ʷ
compile (suc (suc zero)) (a ∷ b ∷ []) t r = [ CCX a b t ]ʷ
compile (suc (suc (suc k))) (a ∷ b ∷ cs) t r =
  [ CCX a b r ]ʷ • compile (suc (suc k)) (r ∷ cs) t a •
  [ CCX a b r ]ʷ • compile (suc (suc k)) (r ∷ cs) t a

controls-cong : ∀ (cs : Vec Wire k) {s u} → s ≈s u → controls cs s ≡ controls cs u
controls-cong [] eq = refl
controls-cong (c ∷ cs) eq = cong₂ _∧_ (eq c) (controls-cong cs eq)

controls-toggle : ∀ (cs : Vec Wire k) t → Fresh t cs →
  ∀ p s → controls cs (toggle t p s) ≡ controls cs s
controls-toggle [] t fresh p s = refl
controls-toggle (a ∷ cs) t (ta , rest) p s =
  cong₂ _∧_ (B.toggle-other (λ eq → ta (sym eq)) p s)
    (controls-toggle cs t rest p s)

controlled-cong : ∀ (cs : Vec Wire k) t {s u} → s ≈s u → controlled cs t s ≈s controlled cs t u
controlled-cong cs t {s} {u} eq i =
  trans (cong (λ b → toggle t b s i) (controls-cong cs eq))
    (B.toggle-cong t (controls cs u) eq i)

act₀-cong : ∀ g {s u} → s ≈s u → act₀ g s ≈s act₀ g u
act₀-cong (X t) = controlled-cong [] t
act₀-cong (CX c t) = controlled-cong (c ∷ []) t
act₀-cong (CCX a b t) = controlled-cong (a ∷ b ∷ []) t

act-cong : ∀ w {s u} → s ≈s u → act w s ≈s act w u
act-cong [ g ]ʷ eq = act₀-cong g eq
act-cong ε eq = eq
act-cong (w • v) eq = act-cong w (act-cong v eq)

private
  recurse-valid : ∀ {a b t r} {cs : Vec Wire k} →
    Valid (a ∷ b ∷ cs) t r → Valid (r ∷ cs) t a
  recurse-valid v = record
    { target≢spare = proj₁ (target-fresh v)
    ; target-fresh = target≢spare v , proj₂ (proj₂ (target-fresh v))
    ; spare-fresh = (λ eq → proj₁ (spare-fresh v) (sym eq)) , proj₂ (proj₁ (distinct v))
    ; distinct = proj₂ (proj₂ (spare-fresh v)) , proj₂ (proj₂ (distinct v))
    }

  join-controls : ∀ a b (cs : Vec Wire k) s →
    controls (a ∷ b ∷ []) s ∧ controls cs s ≡ controls (a ∷ b ∷ cs) s
  join-controls a b cs s = trans
    (cong (_∧ controls cs s) (cong (s a ∧_) (∧-identityʳ (s b))))
    (∧-assoc (s a) (s b) (controls cs s))

private
  step-correct : ∀ k a b (cs : Vec Wire (suc k)) t r →
    (valid : Valid (a ∷ b ∷ cs) t r) →
    (∀ s → act (compile (suc (suc k)) (r ∷ cs) t a) s
      ≈s controlled (r ∷ cs) t s) →
    ∀ s → act (compile (suc (suc (suc k))) (a ∷ b ∷ cs) t r) s
      ≈s controlled (a ∷ b ∷ cs) t s
  step-correct k a b cs t r valid induction s i =
    trans (replace-recursion i)
      (trans (Local.borrowed-bit s i)
        (cong (λ p → toggle t p s i) (join-controls a b cs s)))
    where
    P = controls (a ∷ b ∷ [])
    Q = controls cs

    t-p : Fresh t (a ∷ b ∷ [])
    t-p = proj₁ (target-fresh valid) , proj₁ (proj₂ (target-fresh valid)) , tt
    r-p : Fresh r (a ∷ b ∷ [])
    r-p = proj₁ (spare-fresh valid) , proj₁ (proj₂ (spare-fresh valid)) , tt

    module Local = B.Controls t r (target≢spare valid) P Q
      (controls-toggle (a ∷ b ∷ []) t t-p)
      (controls-toggle (a ∷ b ∷ []) r r-p)
      (controls-toggle cs t (proj₂ (proj₂ (target-fresh valid))))
      (controls-toggle cs r (proj₂ (proj₂ (spare-fresh valid))))

    D = compile (suc (suc k)) (r ∷ cs) t a

    ih : ∀ s → act D s ≈s Local.B s
    ih = induction

    inner : act₀ (CCX a b r) (act D s) ≈s Local.A (Local.B s)
    inner = act₀-cong (CCX a b r) (ih s)

    outer : act D (act₀ (CCX a b r) (act D s)) ≈s Local.B (Local.A (Local.B s))
    outer j = trans (act-cong D inner j) (ih (Local.A (Local.B s)) j)

    replace-recursion : act (compile (suc (suc (suc k))) (a ∷ b ∷ cs) t r) s
      ≈s Local.A (Local.B (Local.A (Local.B s)))
    replace-recursion = act₀-cong (CCX a b r) outer

-- Every input assignment is covered; there is no clean-bit premise.
compile-correct : ∀ k (cs : Vec Wire k) t r → Valid cs t r →
  ∀ s → act (compile k cs t r) s ≈s controlled cs t s
compile-correct zero [] t r valid s i = refl
compile-correct (suc zero) (a ∷ []) t r valid s i = refl
compile-correct (suc (suc zero)) (a ∷ b ∷ []) t r valid s i = refl
compile-correct (suc (suc (suc k))) (a ∷ b ∷ cs) t r valid =
  step-correct k a b cs t r valid
    (compile-correct (suc (suc k)) (r ∷ cs) t a (recurse-valid valid))
