------------------------------------------------------------------------
-- Presentations of groups
--
-- The wires of the ripple-carry adder (Amy, QPL 2018, section 5.2)
--
-- The adder of PathSum.Adder.Ripple works on n = m + 1 bit positions.
-- Its wires are named by Wire b m: the inputs x_i and y_i, the
-- temporary register s_i (i = 0 … m), the carry ancillas c₁ … c_m
-- (cw j holds the carry into position j + 1), the output z₀ … z_(m+1)
-- (n + 1 bits: the sum and the carry out) and, when b is true, a
-- carry-in wire.  The adder itself has no carry in (b = false); the
-- positions after the first form an adder with one, from c₁ -- the
-- inner layout, reached by shift, which names position i + 1 as
-- position i and c₁ as the carry in.  So the netlist and its proof go
-- by recursion on m, one position at a time.
--
-- A layout places the names on the circuit's wires, injectively
-- (Layout); distinct names are then distinct wires, which is all the
-- netlist's gates need.  The inner layout is the layout composed with
-- shift (inner), injective because shift is (it has a partial
-- inverse).  The standard layout puts, on exactly 5n wires,
--
--    x₀ … x_m, y₀ … y_m, z₀ … z_n, c₁ … c_m, s₀ … s_m
--
-- (standard, width-5n; the positions are standard-x … standard-s): the
-- paper's |x⟩|y⟩|0⟩ on the first 3n + 1 wires, the 2n − 1 ancillas
-- after them.  Its injectivity is proved by decoding a wire back to
-- its name (name-place).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Adder.Layout where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Sum.Base using ([_,_]′)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

import Data.Fin.Properties as Fin

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    b : Bool
    m N : ℕ
    W : Set


------------------------------------------------------------------------
-- Names

-- The wires of an adder on m + 1 positions, with a carry in when b.

data Wire (b : Bool) (m : ℕ) : Set where
  cin      : T b → Wire b m
  xw yw sw : Fin (suc m) → Wire b m
  cw       : Fin m → Wire b m
  zw       : Fin (suc (suc m)) → Wire b m

-- The positions after the first, as an adder with carry in c₁.

shift : Wire true m → Wire b (suc m)
shift (cin _) = cw zero
shift (xw i)  = xw (suc i)
shift (yw i)  = yw (suc i)
shift (sw i)  = sw (suc i)
shift (cw j)  = cw (suc j)
shift (zw k)  = zw (suc k)

-- It is injective: this partial inverse undoes it.

private
  unshift : Wire b (suc m) → Maybe (Wire true m)
  unshift (cin _)       = nothing
  unshift (xw zero)     = nothing
  unshift (xw (suc i))  = just (xw i)
  unshift (yw zero)     = nothing
  unshift (yw (suc i))  = just (yw i)
  unshift (sw zero)     = nothing
  unshift (sw (suc i))  = just (sw i)
  unshift (cw zero)     = just (cin tt)
  unshift (cw (suc j))  = just (cw j)
  unshift (zw zero)     = nothing
  unshift (zw (suc k))  = just (zw k)

  unshift-shift : (v : Wire true m) → unshift (shift {b = b} v) ≡ just v
  unshift-shift (cin _) = refl
  unshift-shift (xw i)  = refl
  unshift-shift (yw i)  = refl
  unshift-shift (sw i)  = refl
  unshift-shift (cw j)  = refl
  unshift-shift (zw k)  = refl

shift-injective : (u v : Wire true m) → shift {b = b} u ≡ shift v → u ≡ v
shift-injective u v e = just-injective
  (trans (sym (unshift-shift u)) (trans (cong unshift e) (unshift-shift v)))


------------------------------------------------------------------------
-- Layouts

-- The names placed on N wires, injectively.

record Layout (W : Set) (N : ℕ) : Set where
  field
    wire     : W → Fin N
    wire-inj : ∀ u v → wire u ≡ wire v → u ≡ v

open Layout public

-- The inner layout: the positions after the first, carry in c₁.

inner : Layout (Wire b (suc m)) N → Layout (Wire true m) N
inner L = record
  { wire     = λ v → wire L (shift v)
  ; wire-inj = λ u v e →
      shift-injective u v (wire-inj L (shift u) (shift v) e)
  }


------------------------------------------------------------------------
-- The standard layout

-- For n = m + 1: x (n wires), y (n), z (n + 1), c (m = n − 1), s (n).

width : ℕ → ℕ
width m = suc m + (suc m + (suc (suc m) + (m + suc m)))

width-5n : ∀ m → width m ≡ 5 * suc m
width-5n = solve 1 (λ m → (con 1 :+ m) :+ ((con 1 :+ m) :+ ((con 2 :+ m)
                           :+ (m :+ (con 1 :+ m))))
                         := con 5 :* (con 1 :+ m))
                 refl

private
  -- The blocks after the first, and the names in each.

  B₅ : ℕ → ℕ
  B₅ m = m + suc m

  B₄ B₃ : ℕ → ℕ
  B₄ m = suc (suc m) + B₅ m
  B₃ m = suc m + B₄ m

  place : Wire false m → Fin (width m)
  place     (cin ())
  place {m} (xw i) = i ↑ˡ B₃ m
  place {m} (yw i) = suc m ↑ʳ (i ↑ˡ B₄ m)
  place {m} (zw k) = suc m ↑ʳ (suc m ↑ʳ (k ↑ˡ B₅ m))
  place {m} (cw j) = suc m ↑ʳ (suc m ↑ʳ (suc (suc m) ↑ʳ (j ↑ˡ suc m)))
  place {m} (sw i) = suc m ↑ʳ (suc m ↑ʳ (suc (suc m) ↑ʳ (m ↑ʳ i)))

  -- Decoding, block by block.

  name₅ : Fin (B₅ m) → Wire false m
  name₅ {m} w = [ cw , sw ]′ (splitAt m w)

  name₄ : Fin (B₄ m) → Wire false m
  name₄ {m} w = [ zw , name₅ ]′ (splitAt (suc (suc m)) w)

  name₃ : Fin (B₃ m) → Wire false m
  name₃ {m} w = [ yw , name₄ ]′ (splitAt (suc m) w)

  name : Fin (width m) → Wire false m
  name {m} w = [ xw , name₃ ]′ (splitAt (suc m) w)

  name-place : (v : Wire false m) → name (place v) ≡ v
  name-place     (cin ())
  name-place {m} (xw i) =
    cong [ xw , name₃ ]′ (Fin.splitAt-↑ˡ (suc m) i (B₃ m))
  name-place {m} (yw i) =
    trans (cong [ xw , name₃ ]′
                (Fin.splitAt-↑ʳ (suc m) (B₃ m) (i ↑ˡ B₄ m)))
          (cong [ yw , name₄ ]′ (Fin.splitAt-↑ˡ (suc m) i (B₄ m)))
  name-place {m} (zw k) =
    trans (cong [ xw , name₃ ]′
                (Fin.splitAt-↑ʳ (suc m) (B₃ m) (suc m ↑ʳ (k ↑ˡ B₅ m))))
    (trans (cong [ yw , name₄ ]′
                 (Fin.splitAt-↑ʳ (suc m) (B₄ m) (k ↑ˡ B₅ m)))
           (cong [ zw , name₅ ]′ (Fin.splitAt-↑ˡ (suc (suc m)) k (B₅ m))))
  name-place {m} (cw j) =
    trans (cong [ xw , name₃ ]′
                (Fin.splitAt-↑ʳ (suc m) (B₃ m) (suc m ↑ʳ w₃)))
    (trans (cong [ yw , name₄ ]′ (Fin.splitAt-↑ʳ (suc m) (B₄ m) w₃))
    (trans (cong [ zw , name₅ ]′
                 (Fin.splitAt-↑ʳ (suc (suc m)) (B₅ m) (j ↑ˡ suc m)))
           (cong [ cw , sw ]′ (Fin.splitAt-↑ˡ m j (suc m)))))
    where
    w₃ : Fin (B₄ m)
    w₃ = suc (suc m) ↑ʳ (j ↑ˡ suc m)
  name-place {m} (sw i) =
    trans (cong [ xw , name₃ ]′
                (Fin.splitAt-↑ʳ (suc m) (B₃ m) (suc m ↑ʳ w₃)))
    (trans (cong [ yw , name₄ ]′ (Fin.splitAt-↑ʳ (suc m) (B₄ m) w₃))
    (trans (cong [ zw , name₅ ]′
                 (Fin.splitAt-↑ʳ (suc (suc m)) (B₅ m) (m ↑ʳ i)))
           (cong [ cw , sw ]′ (Fin.splitAt-↑ʳ m (suc m) i))))
    where
    w₃ : Fin (B₄ m)
    w₃ = suc (suc m) ↑ʳ (m ↑ʳ i)

-- The standard layout of the adder on n = m + 1 bits.

standard : (m : ℕ) → Layout (Wire false m) (width m)
standard m = record
  { wire     = place
  ; wire-inj = λ u v e →
      trans (sym (name-place u)) (trans (cong name e) (name-place v))
  }

-- Where the wires are: x_i at i, y_i at n + i, z_k at 2n + k, c_(j+1)
-- at 3n + 1 + j, s_i at 4n + i.

standard-x : ∀ m (i : Fin (suc m)) → toℕ (wire (standard m) (xw i)) ≡ toℕ i
standard-x m i = Fin.toℕ-↑ˡ i (B₃ m)

standard-y : ∀ m (i : Fin (suc m)) →
             toℕ (wire (standard m) (yw i)) ≡ suc m + toℕ i
standard-y m i =
  trans (Fin.toℕ-↑ʳ (suc m) (i ↑ˡ B₄ m))
        (cong (suc m +_) (Fin.toℕ-↑ˡ i (B₄ m)))

standard-z : ∀ m (k : Fin (suc (suc m))) →
             toℕ (wire (standard m) (zw k)) ≡ suc m + (suc m + toℕ k)
standard-z m k =
  trans (Fin.toℕ-↑ʳ (suc m) (suc m ↑ʳ (k ↑ˡ B₅ m)))
        (cong (suc m +_) (trans (Fin.toℕ-↑ʳ (suc m) (k ↑ˡ B₅ m))
                                (cong (suc m +_) (Fin.toℕ-↑ˡ k (B₅ m)))))

standard-c : ∀ m (j : Fin m) →
             toℕ (wire (standard m) (cw j)) ≡
             suc m + (suc m + (suc (suc m) + toℕ j))
standard-c m j =
  trans (Fin.toℕ-↑ʳ (suc m) (suc m ↑ʳ w₃))
  (cong (suc m +_) (trans (Fin.toℕ-↑ʳ (suc m) w₃)
  (cong (suc m +_) (trans (Fin.toℕ-↑ʳ (suc (suc m)) (j ↑ˡ suc m))
                          (cong (suc (suc m) +_) (Fin.toℕ-↑ˡ j (suc m)))))))
  where
  w₃ : Fin (B₄ m)
  w₃ = suc (suc m) ↑ʳ (j ↑ˡ suc m)

standard-s : ∀ m (i : Fin (suc m)) →
             toℕ (wire (standard m) (sw i)) ≡
             suc m + (suc m + (suc (suc m) + (m + toℕ i)))
standard-s m i =
  trans (Fin.toℕ-↑ʳ (suc m) (suc m ↑ʳ w₃))
  (cong (suc m +_) (trans (Fin.toℕ-↑ʳ (suc m) w₃)
  (cong (suc m +_) (trans (Fin.toℕ-↑ʳ (suc (suc m)) (m ↑ʳ i))
                          (cong (suc (suc m) +_) (Fin.toℕ-↑ʳ m i))))))
  where
  w₃ : Fin (B₄ m)
  w₃ = suc (suc m) ↑ʳ (m ↑ʳ i)
