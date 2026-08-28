------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): traversing the X-normal
-- staircase.
--
-- Pushing gives the rules for one dirty gate meeting one D or E box.
-- This module puts them together along a whole M(n), which is where the
-- staircase's shape starts to pay off.
--
-- The first result is the one the rest of the M side rests on: an S
-- entering at the bottom of a staircase walks straight up it to the E
-- box, changing nothing on the way.
--
--   altSIDD  S·D_ℓ = D_ℓ·S for all four D boxes, with the S moved from
--            the box's qubit 0 to its qubit 1 -- up one wire -- with no
--            phase and nothing else emitted.
--   altSE    S·E_h = E_{h+1}.
--
-- M(n)'s boxes sit on (0,1), (1,2), ..., so an S leaving one box at its
-- upper wire arrives at the next at its lower wire and the same rule
-- fires again; at the top it meets E.  So the traversal of the whole
-- staircase is: the E box advances by the number of S's, no D box
-- changes, no ω is produced and nothing escapes.
--
-- That is the whole reason the E box is where the paper puts it.  It
-- also settles, for this case, the invariant Tower flags -- that what
-- escapes a level must not touch the top wire -- because nothing
-- escapes at all: the S is absorbed by E, which is exactly the box
-- sitting on the top wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.PushingM
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Fin using (Fin) renaming (zero to fz ; suc to fs)
open import Data.List using (List ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_)

open import Notations using (₁₊ ; ₂₊)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime
  using (Circuit ; H ; S ; X ; CZ ; _↑)
open import Examples.Groups.Clifford.Qubit.Selinger.PushingD p-2 p-prime
  using (pushZZ-DD)
open import Examples.Groups.Clifford.Qubit.Selinger.Normal p-2 p-prime
  using (Mx)
open import ForStdlib.Data.Fin.Mod using (ℤ)

open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using ( Dirty ; Dirty⁺
        ; H₀ ; S₀ ; X₀ ; H₁ ; S₁ ; X₁ ; H₂ ; S₂ ; ZZ₀₁ ; ZZ₁₂
        ; pushZZD ; pushS₁D ; pushH₁D )

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The E box counts S gates
--
-- E₁, E₂, E₃, E₄ are ε, S, S², S³, so an S advances the box by one and
-- E₄ wraps to E₁.  This is altSE, read as a successor.

succE : EBox → EBox
succE e₁ = e₂
succE e₂ = e₃
succE e₃ = e₄
succE e₄ = e₁

stepE : ℕ → EBox → EBox
stepE 0       e = e
stepE (₁₊ k) e = stepE k (succE e)

------------------------------------------------------------------------
-- S gates entering the bottom of a staircase
--
-- Every D box passes the S on unchanged, so the recursion carries the
-- count up untouched and spends it all at the E box.  No phase, no
-- escaping dirt, and the D boxes are returned as they came.

pushS-Mx : ℕ → Mx n → Mx n
pushS-Mx {0}    k e       = stepE k e
pushS-Mx {₁₊ n} k (d , m) = d , pushS-Mx k m

-- The staircase of the identity -- all D₁ and E₁, as in (6.4) -- is
-- Tower.mx-id, and is not repeated here.  Pushing k S gates into it
-- returns it with E advanced, which is the M-side of the one-qubit
-- action generalised: at n = 0 this is exactly Rewrite's pushE.

------------------------------------------------------------------------
-- Splitting the dirt a D box emits
--
-- Which way a gate goes is decided by its subscript, and the rules make
-- the two directions completely different.
--
-- Subscript 1 is the box's UPPER wire, and the gate continues into the
-- rest of the staircase -- where it will meet the next box at ITS qubit
-- 0.  The only qubit-0 rule is altSIDD, which takes an S, so an S is the
-- only thing that can ascend; a D box that emitted an H upwards would
-- have nowhere to send it.  That is why ascending dirt is a COUNT.
--
-- Subscript 0 is the lower wire, below everything the staircase has
-- left, so those gates escape.  They are kept in order, as a word.

-- Every constructor is listed rather than caught by a wildcard.  The D
-- rules emit only H₀, S₀ and S₁ -- checked against all sixteen clauses
-- of altIHDD, altISDD, altSIDD and altZZDD -- so the other seven cases
-- cannot arise; but a wildcard would DROP one silently if a rule were
-- ever mistranscribed, and dropping a gate is a soundness bug that
-- nothing here would catch.  Written out, a surprise shows up instead
-- as a clause that is visibly wrong.

ascS : List Dirty → ℕ
ascS []         = 0
ascS (S₁ ∷ ds) = ₁₊ (ascS ds)
-- escaping, counted by esc
ascS (H₀ ∷ ds) = ascS ds
ascS (S₀ ∷ ds) = ascS ds
ascS (X₀ ∷ ds) = ascS ds
-- not emitted by any D rule
ascS (H₁ ∷ ds) = ascS ds
ascS (X₁ ∷ ds) = ascS ds
ascS (ZZ₀₁ ∷ ds) = ascS ds

esc : List Dirty → List Dirty
esc []         = []
esc (H₀ ∷ ds) = H₀ ∷ esc ds
esc (S₀ ∷ ds) = S₀ ∷ esc ds
esc (X₀ ∷ ds) = X₀ ∷ esc ds
-- ascending, counted by ascS
esc (S₁ ∷ ds) = esc ds
-- not emitted by any D rule
esc (H₁ ∷ ds) = esc ds
esc (X₁ ∷ ds) = esc ds
esc (ZZ₀₁ ∷ ds) = esc ds

------------------------------------------------------------------------
-- A dirty gate meeting the bottom box of a staircase
--
-- All four D families have the same shape once the split above is in
-- place: rewrite the bottom box by the rule, carry the ascending S
-- gates to the E box with pushS-Mx, and hand back what escapes.  The
-- rule is the only thing that differs, so it is a parameter.
--
-- The phase is returned rather than dropped even though every D rule is
-- phase-free, so that the caller is not relying on that.

push-bottom : (DBox → ℤ 8 × DBox × List Dirty) →
              Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
push-bottom rule (d , m) with rule d
... | k , d′ , out = k , esc out , (d′ , pushS-Mx (ascS out) m)

-- A controlled-Z on the staircase's bottom pair (altZZDD).  D₁ and D₄
-- simply swap and emit nothing at all.
pushZZ-Mx : Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
pushZZ-Mx = push-bottom pushZZD

-- An S arriving on the upper wire of the bottom box (altISDD).  This is
-- what a C₂ box sends into the staircase, via commZZCI's trailing S
-- gates.
pushS₁-Mx : Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
pushS₁-Mx = push-bottom pushS₁D

-- An H arriving on the upper wire of the bottom box (altIHDD).
pushH₁-Mx : Mx (₁₊ n) → ℤ 8 × List Dirty × Mx (₁₊ n)
pushH₁-Mx = push-bottom pushH₁D

------------------------------------------------------------------------
-- Escaping dirt, as a circuit
--
-- What escapes a box does so on its lower wire, and nothing the
-- staircase has left touches that wire again, so it can be realised
-- straight away.  X is the derived word HS²H of §4.
--
-- Only the subscript-0 gates are realised; S₁ has already been counted
-- by ascS, and the remaining seven cannot occur (see the note on that
-- split).  Every constructor is listed for the same reason it is there.

escAt0 : List Dirty → Circuit (₁₊ n)
escAt0 []         = ε
escAt0 (H₀ ∷ ds) = H • escAt0 ds
escAt0 (S₀ ∷ ds) = S • escAt0 ds
escAt0 (X₀ ∷ ds) = X • escAt0 ds
-- ascending, counted by ascS
escAt0 (S₁ ∷ ds) = escAt0 ds
-- not emitted by any D rule
escAt0 (H₁ ∷ ds) = escAt0 ds
escAt0 (X₁ ∷ ds) = escAt0 ds
escAt0 (ZZ₀₁ ∷ ds) = escAt0 ds

------------------------------------------------------------------------
-- An S arriving anywhere on the staircase
--
-- pushS-Mx handles an S that arrives at the bottom.  One arriving at
-- wire j does something different: it meets D(j-1,j) at that box's
-- qubit 1, which is altISDD, and only what that rule sends upwards
-- ascends to the E box.  What it sends down escapes at wire j-1.
--
-- Three cases, and the level decides which:
--
--   level 0     no box has the S at its qubit 1, so it just ascends
--   level 1     the bottom box meets it, by altISDD
--   level 2+    the bottom box does not touch wire j at all, so the S
--               commutes past it and the same question is asked one
--               wire up
--
-- The level is a Fin, so "above the top wire" is not a case that has to
-- be answered: a staircase on ₁₊ n wires admits levels 0 to n, which is
-- Fin (₁₊ n) exactly.  With ℕ there would be an unreachable clause to
-- fill in, and filling it in with anything at all would be a place for a
-- silent wrong answer to hide.
--
-- All of altISDD is phase-free, so no ω is returned.
--
-- The three qubit-1 families share this shape completely, because all
-- of them emit only S gates upward: altISDD's S₁², altIHDD's S₁² and
-- altZZDD's S₁³ and S₁ are the whole of it.  So the ascending part
-- always collapses to a count, and the rule is the only thing that
-- varies -- it becomes a parameter, exactly as at the bottom.

-- The box a gate at wire j+1 meets, counted from the bottom.  A
-- staircase on ₁₊ n wires has n boxes, so this is Fin n, and at n = 0
-- there are none -- which is why the recursion below needs no base case
-- for the empty staircase.
push-q1-at : (DBox → ℤ 8 × DBox × List Dirty) →
             Fin n → Mx n → Circuit n × Mx n
push-q1-at {₁₊ n} rule fz     (d , m) with rule d
... | _ , d′ , out = escAt0 out , (d′ , pushS-Mx (ascS out) m)
push-q1-at {₁₊ n} rule (fs j) (d , m) with push-q1-at rule j m
... | e , m′ = e ↑ , (d , m′)

-- An S anywhere: at the bottom it ascends untouched, higher up it is a
-- qubit-1 encounter with the box below it.
pushS-at : Fin (₁₊ n) → Mx n → Circuit n × Mx n
pushS-at fz     m = ε , pushS-Mx 1 m
pushS-at (fs j) m = push-q1-at pushS₁D j m

-- An H, which has no level-0 case at all: there is no rule for an H
-- meeting a D box at its qubit 0, so an H can only arrive above the
-- bottom wire.  Fin n says exactly that -- one fewer level than the S
-- case, and none at all on a one-wire staircase.
pushH-at : Fin n → Mx n → Circuit n × Mx n
pushH-at = push-q1-at pushH₁D

------------------------------------------------------------------------
-- Escaping dirt across two wires
--
-- The two-box rules leave dirt on both wires of the lower box and a
-- controlled-Z on that pair, all of which is below everything the
-- staircase has left, so all of it escapes.  Only the wire-2 gates
-- continue, and those are S gates, counted separately.

escAt01 : List Dirty⁺ → Circuit (₂₊ n)
escAt01 []         = ε
escAt01 (H₀ ∷ ds) = H • escAt01 ds
escAt01 (S₀ ∷ ds) = S • escAt01 ds
escAt01 (X₀ ∷ ds) = X • escAt01 ds
escAt01 (H₁ ∷ ds) = H ↑ • escAt01 ds
escAt01 (S₁ ∷ ds) = S ↑ • escAt01 ds
escAt01 (X₁ ∷ ds) = X ↑ • escAt01 ds
escAt01 (ZZ₀₁ ∷ ds) = CZ • escAt01 ds
-- ascending, counted by ascS₂
escAt01 (S₂ ∷ ds) = escAt01 ds
-- not emitted by altIZZDDIIDD
escAt01 (H₂ ∷ ds) = escAt01 ds
escAt01 (ZZ₁₂ ∷ ds) = escAt01 ds

ascS₂ : List Dirty⁺ → ℕ
ascS₂ []         = 0
ascS₂ (S₂ ∷ ds) = ₁₊ (ascS₂ ds)
ascS₂ (_  ∷ ds) = ascS₂ ds

------------------------------------------------------------------------
-- A controlled-Z arriving anywhere on the staircase
--
-- At the bottom it spans the pair of D(0,1) and meets that box alone,
-- which is the local altZZDD.  At (j,j+1) for j ≥ 1 it spans D(j,j+1)
-- while also sharing wire j with D(j-1,j), so it meets both and needs
-- altIZZDDIIDD.  Higher still it touches neither of the bottom boxes and
-- commutes past.
--
-- The levels are Fin n: a controlled-Z needs a box on its own pair, and
-- a staircase on ₁₊ n wires has boxes on (0,1) up to (n-1,n), so j runs
-- to n-1.  A one-wire staircase has none, and Fin 0 is empty.

pushZZ-at : Fin n → Mx n → ℤ 8 × Circuit n × Mx n
pushZZ-at {₁₊ n} fz m with pushZZ-Mx m
... | k , o , m′ = k , escAt0 o , m′
-- The two boxes are named dl and du, not d₀ and d₁: d₁ is a DBox
-- CONSTRUCTOR, so a pattern variable of that name silently matches only
-- the d₁ box and the other three clauses go missing.  The coverage
-- checker caught it, which on this development is worth recording --
-- it is the first of these mistakes the types have found.
pushZZ-at {₂₊ n} (fs fz) (dl , du , m) with pushZZ-DD dl du
... | k , (dl′ , du′) , out =
  k , escAt01 out , (dl′ , du′ , pushS-Mx (ascS₂ out) m)
pushZZ-at {₂₊ n} (fs (fs j)) (d , m) with pushZZ-at (fs j) m
... | k , e , m′ = k , e ↑ , (d , m′)

------------------------------------------------------------------------
-- What cannot arrive at the BOTTOM
--
-- There is no rule for an H, or an X, meeting a D box at its qubit 0,
-- and the omission is not an oversight of the paper's: nothing delivers
-- one to the bottom of a staircase.  Dirt arriving there comes from the
-- C box on its left, and the C rules (commXC, commSC, commZZCI) emit
-- only S gates and controlled-Zs.  Both are handled above.
--
-- This says nothing about the rest of the staircase.  Dirt on higher
-- wires commutes past the C box and meets M(n) at its own level, so the
-- boxes above the bottom one can be met by gates this module does not
-- treat; see the note in PushingCM.  Everything here is the level-0
-- case.
--
-- Definition 6.1's wire labelling is what will make the general case
-- finite, and when h is assembled it has to become an invariant of the
-- traversal rather than a remark in a comment.
