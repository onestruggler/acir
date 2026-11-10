------------------------------------------------------------------------
-- Presentations of groups
--
-- Four wires: the steps a derivation from the rules (1)–(7) is made of
--
-- On four wires a letter is a gate on the bottom three wires, on the
-- top three, or both, so a derivation needs just two kinds of step
-- besides the rules that are properly about four wires:
--
-- * bot l r and top l r: two three-wire circuits with the same
--   function, on the bottom three wires and on the top three.  They
--   are equal by the rules, because the rules are complete on three
--   wires (ThreeWire); the evidence is a boolean computed on the eight
--   states.
--
-- * rule (7) (r7⁼), the naturality of the swap at CCX (nat-ccx⁼), and
--   the commutations of a gate that touches wire 0 with a gate that
--   touches wire 3 and no wire of the first (comm-…): the instances of
--   the rules that involve all four wires.
--
-- These are equations of the engine (Engine), used by rw in the
-- derivations of the relations of Syntactics from the rules (Frames,
-- Four.Part*, Four.Relations, Equivalence).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.FourWire where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Alt16-RevCir.Semantics using (same ; same-sound)
open import Examples.Groups.Alt16-RevCir.Syntactics
  using ( Gen ; X-gate ; CX-gate ; Ex-gate ; CCX-gate
        ; X-gen ; CX-gen ; Ex-gen ; CCX-gen ; _↥ ; _↧ᵏ_ ; _↓ᵏ_
        ; σ-nat₃ )
open import Examples.Groups.Alt16-RevCir.Theory
  using (_TRel,_===_ ; r7 ; module T)
open import Examples.Groups.Alt16-RevCir.ThreeWire using (complete₃)

open import Examples.Groups.Alt16-RevCir.Engine _TRel,_===_ public

------------------------------------------------------------------------
-- Three-wire steps

-- Two three-wire circuits with the same function.
sem₃ : (l r : List (Gen 3)) → same 3 ⟪ l ⟫ ⟪ r ⟫ ≡ true → Eqn 3
sem₃ l r h = eqn l r (complete₃ (same-sound ⟪ l ⟫ ⟪ r ⟫ h))

-- ... on the top three wires of four,
top : (l r : List (Gen 3)) → same 3 ⟪ l ⟫ ⟪ r ⟫ ≡ true → Eqn 4
top l r h = lift⁼ (sem₃ l r h)

private
  -- Widening the letters widens the word.
  ⟪map↧⟫ : (xs : List (Gen 3)) → ⟪ map (_↧ᵏ 1) xs ⟫ ≡ ⟪ xs ⟫ ↓ᵏ 1
  ⟪map↧⟫ []       = refl
  ⟪map↧⟫ (x ∷ xs) = Eq.cong ([ x ↧ᵏ 1 ]ʷ •_) (⟪map↧⟫ xs)

-- ... and on the bottom three.
bot : (l r : List (Gen 3)) → same 3 ⟪ l ⟫ ⟪ r ⟫ ≡ true → Eqn 4
bot l r h = eqn (map (_↧ᵏ 1) l) (map (_↧ᵏ 1) r)
  (Eq.subst₂ (T._⊢_≈_ 4) (Eq.sym (⟪map↧⟫ l)) (Eq.sym (⟪map↧⟫ r))
             (T.pad₃ (prf (sem₃ l r h)) 1))

------------------------------------------------------------------------
-- The letters on four wires

x0 x1 x2 x3 cx0 cx1 cx2 ex0 ex1 ex2 ccx0 ccx1 : Gen 4
x0   = X-gen
x1   = X-gen ↥
x2   = X-gen ↥ ↥
x3   = X-gen ↥ ↥ ↥
cx0  = CX-gen
cx1  = CX-gen ↥
cx2  = CX-gen ↥ ↥
ex0  = Ex-gen
ex1  = Ex-gen ↥
ex2  = Ex-gen ↥ ↥
ccx0 = CCX-gen
ccx1 = CCX-gen ↥

------------------------------------------------------------------------
-- The rules on four wires

-- Rule (7).
r7⁼ : Eqn 4
r7⁼ = eqnʷ (ccx1 ∷ cx0 ∷ ccx1 ∷ []) (ex0 ∷ ccx1 ∷ ex0 ∷ cx0 ∷ [])
  (PB.axiom (T.srel (T.srel r7))) refl refl

-- CCX followed by the cycle of the four wires is the cycle followed by
-- CCX one wire up.
nat-ccx⁼ : Eqn 4
nat-ccx⁼ = eqnʷ (ccx0 ∷ ex2 ∷ ex1 ∷ ex0 ∷ []) (ex2 ∷ ex1 ∷ ex0 ∷ ccx1 ∷ [])
  (T.sym-rule (σ-nat₃ CCX-gate)) refl refl

-- A gate that touches wire 0 commutes with one that touches wire 3 on
-- other wires.
comm-x3-x0 comm-cx2-x0 comm-ex2-x0 comm-ccx1-x0 : Eqn 4
comm-x3-x0 = eqnʷ (x3 ∷ x0 ∷ []) (x0 ∷ x3 ∷ [])
  (PB.axiom (T.comm₁ X-gate (X-gen ↥ ↥))) refl refl
comm-cx2-x0 = eqnʷ (cx2 ∷ x0 ∷ []) (x0 ∷ cx2 ∷ [])
  (PB.axiom (T.comm₁ X-gate (CX-gen ↥))) refl refl
comm-ex2-x0 = eqnʷ (ex2 ∷ x0 ∷ []) (x0 ∷ ex2 ∷ [])
  (PB.axiom (T.comm₁ X-gate (Ex-gen ↥))) refl refl
comm-ccx1-x0 = eqnʷ (ccx1 ∷ x0 ∷ []) (x0 ∷ ccx1 ∷ [])
  (PB.axiom (T.comm₁ X-gate CCX-gen)) refl refl

comm-x3-cx0 comm-cx2-cx0 comm-ex2-cx0 : Eqn 4
comm-x3-cx0 = eqnʷ (x3 ∷ cx0 ∷ []) (cx0 ∷ x3 ∷ [])
  (PB.axiom (T.comm₂ CX-gate (X-gen ↥))) refl refl
comm-cx2-cx0 = eqnʷ (cx2 ∷ cx0 ∷ []) (cx0 ∷ cx2 ∷ [])
  (PB.axiom (T.comm₂ CX-gate CX-gen)) refl refl
comm-ex2-cx0 = eqnʷ (ex2 ∷ cx0 ∷ []) (cx0 ∷ ex2 ∷ [])
  (PB.axiom (T.comm₂ CX-gate Ex-gen)) refl refl

comm-x3-ex0 comm-cx2-ex0 comm-ex2-ex0 : Eqn 4
comm-x3-ex0 = eqnʷ (x3 ∷ ex0 ∷ []) (ex0 ∷ x3 ∷ [])
  (PB.axiom (T.comm₂ Ex-gate (X-gen ↥))) refl refl
comm-cx2-ex0 = eqnʷ (cx2 ∷ ex0 ∷ []) (ex0 ∷ cx2 ∷ [])
  (PB.axiom (T.comm₂ Ex-gate CX-gen)) refl refl
comm-ex2-ex0 = eqnʷ (ex2 ∷ ex0 ∷ []) (ex0 ∷ ex2 ∷ [])
  (PB.axiom (T.comm₂ Ex-gate Ex-gen)) refl refl

comm-x3-ccx0 : Eqn 4
comm-x3-ccx0 = eqnʷ (x3 ∷ ccx0 ∷ []) (ccx0 ∷ x3 ∷ [])
  (PB.axiom (T.comm₃ CCX-gate X-gen)) refl refl

------------------------------------------------------------------------
-- A first use: CX on the bottom wires commutes with the Toffoli gate
-- from the top two wires onto wire 0
--
-- With T the Toffoli gate one wire up, c the bottom CX and Q the
-- Toffoli gate with controls 2 3 and target 0, rule (7) says
-- T c T = Q c, so Q = T c T c; Q is an involution (a fact about three
-- wires), hence (T c)⁴ = ε, which is what c Q = Q c comes to.  The
-- generated derivations (Four.Part*) are lists of steps like this one.

private
  cx ex ccx : Gen 3
  cx  = CX-gen
  ex  = Ex-gen
  ccx = CCX-gen

comm-cx0-Q : Eqn 4
comm-cx0-Q = derive
  (cx0 ∷ ex0 ∷ ccx1 ∷ ex0 ∷ [])
  (ex0 ∷ ccx1 ∷ ex0 ∷ cx0 ∷ [])
  -- c Q → c Q c c → c (T c T) c
  ( rw 4 (sym⁼ (bot (cx ∷ cx ∷ []) [] refl))
  ∷ rw 1 (sym⁼ r7⁼)
  -- → Q Q c T c T c:  put Q Q, the identity, in front
  ∷ rw 0 (sym⁼ QQ)
  -- the second Q with what follows it, Q c, is T c T
  ∷ rw 3 (sym⁼ r7⁼)
  -- now Q (T c T) (T c T) c: the inner T T and c c cancel
  ∷ rw 5 (top (ccx ∷ ccx ∷ []) [] refl)
  ∷ rw 4 (bot (cx ∷ cx ∷ []) [] refl)
  ∷ rw 3 (top (ccx ∷ ccx ∷ []) [] refl)
  ∷ [])
  refl
  where
  -- Q Q = ε: the swaps cancel on the bottom wires, the Toffoli gates
  -- on the top wires.
  QQ : Eqn 4
  QQ = derive
    (ex0 ∷ ccx1 ∷ ex0 ∷ ex0 ∷ ccx1 ∷ ex0 ∷ []) []
    ( rw 2 (bot (ex ∷ ex ∷ []) [] refl)
    ∷ rw 1 (top (ccx ∷ ccx ∷ []) [] refl)
    ∷ rw 0 (bot (ex ∷ ex ∷ []) [] refl)
    ∷ [])
    refl
