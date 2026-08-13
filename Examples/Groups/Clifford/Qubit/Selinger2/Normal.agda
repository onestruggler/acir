------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's normal forms (arXiv:1310.6813, Definition 4.3 and the
-- normal form (4.5)): Z-normal L(n), X-normal M(n), and the normal
-- circuits N(n).
--
-- Syntax only.  Each shape is given as the DATA that determines it,
-- together with the circuit it denotes; that a circuit in this shape is
-- unique for its Clifford operator is §5, and reducing an arbitrary
-- circuit to one is §6.
--
-- The shapes, in the paper's picture (qubits numbered from the top):
--
--   L(n)   an Aᵢ on some qubit, then Bⱼ boxes on successive adjacent
--          pairs descending to the last qubit, then a C_k there.  The
--          number of B boxes is m-1 for 1 ⩽ m ⩽ n, so the A may sit
--          anywhere and the B stack reaches down from it.
--
--   M(n)   D_ℓ boxes on every adjacent pair, a full staircase from the
--          last pair up to the first, then an E_h on qubit 0.  Unlike
--          L(n) this has no free length: n-1 D boxes and one E.
--
--   N(n)   L(n)·M(n) followed by N(n-1) on all but one qubit, and a
--          final ω^p with p ∈ {0,…,7}.
--
-- Orientation.  As in Boxes, qubit 0 of the paper is the un-shifted
-- wire here and _↑ climbs.  The paper's L(n) stack descends to its last
-- qubit and its M(n) staircase climbs to its first; read through that
-- correspondence both run from the un-shifted wire outwards, which is
-- what makes the two recursions below the natural ones.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger2.Normal where

open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)

open import Notations using (₁₊ ; ₂₊)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import Examples.Groups.Clifford.Qubit.Selinger2.Figure8
  using ( Circuit ; Gen ; gate₀ ; gate₁ ; gate₂ ; _↥ ; _↑ ; ω )
open import Examples.Groups.Clifford.Qubit.Selinger2.Boxes

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Widening a circuit by one wire on top
--
-- The recursion for N(n) puts an (n-1)-qubit normal form beside one
-- untouched qubit, so it needs to read a Circuit n as a Circuit (₁₊ n)
-- acting on the same wires.  This is Circuit.Base's _↧ᵏ_ at k = 1, but
-- that lands in Gen (n + 1) and the recursion wants Gen (₁₊ n); the two
-- agree only up to an induction on n, so the successor form is given
-- directly.  Gates keep their wires (their indices are polymorphic in
-- the width); only the shift tower is rebuilt.
--
-- This is also the subgroup embedding of the coset tower: the width-n
-- Clifford circuits sit inside the width-(₁₊ n) ones as those that
-- leave the outermost wire alone.

widen-gen : Gen n → Gen (₁₊ n)
widen-gen (gate₀ h) = gate₀ h
widen-gen (gate₁ h) = gate₁ h
widen-gen (gate₂ h) = gate₂ h
widen-gen (g ↥)     = widen-gen g ↥

widen : Circuit n → Circuit (₁₊ n)
widen ε         = ε
widen [ g ]ʷ    = [ widen-gen g ]ʷ
widen (w • v)   = widen w • widen v

------------------------------------------------------------------------
-- Z-normal circuits (Definition 4.3, first half)

-- The A-and-B part of a Z-normal circuit on ₁₊ n wires.  Either the A
-- sits on the un-shifted wire and there are no B boxes (the paper's
-- m = 1), or a B box occupies the bottom pair and the rest of the stack
-- stands above it.  The stack's height is the paper's m-1.
Chain : ℕ → Set
Chain 0      = ABox
Chain (₁₊ n) = ABox ⊎ (BBox × Chain n)

-- Read outwards: the A runs first, then the B boxes descending to the
-- un-shifted wire, which is the order the paper draws them in.
[_]ᶜʰ : Chain n → Circuit (₁₊ n)
[_]ᶜʰ {0}    a              = [ a ]ᴬ
[_]ᶜʰ {₁₊ n} (inj₁ a)       = [ a ]ᴬ
[_]ᶜʰ {₁₊ n} (inj₂ (b , c)) = [ c ]ᶜʰ ↑ • [ b ]ᴮ

-- A Z-normal circuit is such a stack followed by a C box on the wire
-- the stack reaches.
Lz : ℕ → Set
Lz n = Chain n × CBox

[_]ᴸ : Lz n → Circuit (₁₊ n)
[ ch , c ]ᴸ = [ ch ]ᶜʰ • [ c ]ᶜ

------------------------------------------------------------------------
-- X-normal circuits (Definition 4.3, second half)

-- One D box per adjacent pair and an E box at the far end: on ₁₊ n
-- wires that is n D boxes and one E, with no choice of length.
Mx : ℕ → Set
Mx 0      = EBox
Mx (₁₊ n) = DBox × Mx n

[_]ᴹ : Mx n → Circuit (₁₊ n)
[_]ᴹ {0}    e       = [ e ]ᴱ
[_]ᴹ {₁₊ n} (d , m) = [ d ]ᴰ • [ m ]ᴹ ↑

------------------------------------------------------------------------
-- Normal circuits (4.5)

-- The body: L(n)·M(n), then the same one wire smaller.  The paper's
-- picture is L(n) M(n) L(n-1) M(n-1) … L(1) M(1), which is this
-- recursion read outwards.
NFbody : ℕ → Set
NFbody 0      = ⊤
NFbody (₁₊ n) = Lz n × Mx n × NFbody n

[_]ᴺᵇ : NFbody n → Circuit n
[_]ᴺᵇ {0}    tt          = ε
[_]ᴺᵇ {₁₊ n} (l , m , b) = [ l ]ᴸ • [ m ]ᴹ • widen [ b ]ᴺᵇ

-- A normal circuit is a body followed by a power of the scalar,
-- p ∈ {0,…,7}.  ω is 0-ary, so it needs no wire and this is the one
-- part of the normal form that survives at width 0.
NF : ℕ → Set
NF n = NFbody n × Fin 8

[_]ᴺ : NF n → Circuit n
[ b , p ]ᴺ = [ b ]ᴺᵇ • ω ^ toℕ p
