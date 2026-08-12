------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): the coset tower.
--
-- §6 reduces a circuit to normal form by rewriting.  Following
-- Symplectic instead, the reduction is packaged as a tower of coset
-- extensions: Normalization.CosetNF.SingleLevel turns one level of
-- coset data into a normal form for the wider presentation, and the
-- tower iterates that up the wire count.
--
-- The fit is exact, and it is the shape of Definition 4.3 that makes it
-- so.  A normal circuit on ₁₊ n wires is
--
--     L(n) · M(n) · N(n-1)
--
-- with N(n-1) on the lower n wires.  Read as a coset decomposition, the
-- subgroup is the width-n presentation, the coset is the pair of blocks
-- L(n), M(n), and the Schreier section of a coset is the circuit those
-- blocks denote.  SingleLevel's parameters are then:
--
--   Γ    the width-n relation      (the subgroup)
--   Δ    the width-₁₊ n relation   (the group)
--   C    Lz n × Mx n               (the cosets)
--   I    the identity coset        (6.4)
--   f    widen                     (a width-n generator, one wire up)
--   [_]  section                   ([ l ]ᴸ • [ m ]ᴹ)
--   h    the coset action          (§6's rewrite rules)
--
-- All of these are given below except h, which is where the rule tables
-- of Rewrite, Pushing and PushingZ are assembled, and which is the next
-- piece of work.
--
-- What the tower buys, and why it is worth the detour: SingleLevel
-- derives the normal form, its section, and injectivity from the coset
-- data plus five hypotheses, so §5 (existence and uniqueness) does not
-- have to be proved directly.  The paper's Lemma 6.2 termination
-- argument is likewise not needed -- h is a function, and the tower
-- recurses on the wire count.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.Tower
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Fin using (toℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (inj₂)
open import Data.Unit using (⊤ ; tt)

open import ForStdlib.Data.Fin.Mod using (₀)
open import Notations using (₁₊)
open import Word.Base using ([_]ʷ ; Word ; _•_ ; _^_)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime
  using (Circuit ; Gen ; ω)
import Examples.Groups.Clifford.Qubit.Selinger.Rewrite p-2 p-prime as Rw
open import Examples.Groups.Clifford.Qubit.Selinger.Normal p-2 p-prime
  using (Chain ; Lz ; Mx ; [_]ᴸ ; [_]ᴹ ; widen-gen)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The cosets of one level
--
-- The blocks L(n) and M(n) of Definition 4.3, taken together.  A coset
-- is what distinguishes two normal circuits with the same tail, which
-- is exactly the data SingleLevel asks for.

Coset : ℕ → Set
Coset n = Lz n × Mx n

------------------------------------------------------------------------
-- The identity coset (6.4)
--
-- Proposition 6.3 starts by writing the identity in normal form: an A₁
-- under a FULL stack of B₁ boxes, capped by C₁, and a full staircase of
-- D₁ boxes ending in E₁.  The stack is full -- the A sits on the last
-- wire, not the first -- which is the m = n end of Definition 4.3's
-- range, and is what makes this the identity rather than merely some
-- normal form.

chain-id : ∀ n → Chain n
chain-id 0      = a₁
chain-id (₁₊ n) = inj₂ (b₁ , chain-id n)

mx-id : ∀ n → Mx n
mx-id 0      = e₁
mx-id (₁₊ n) = d₁ , mx-id n

I : ∀ n → Coset n
I n = (chain-id n , c₁) , mx-id n

------------------------------------------------------------------------
-- The Schreier section
--
-- A coset is represented by the circuit its two blocks denote, in the
-- order Definition 4.3 gives them.

section : Coset n → Circuit (₁₊ n)
section (l , m) = [ l ]ᴸ • [ m ]ᴹ

------------------------------------------------------------------------
-- The generator embedding
--
-- A generator of the subgroup is a width-n generator read at width
-- ₁₊ n, on the same wires: the N(n-1) block of a normal circuit sits on
-- the lower n wires and leaves the top one alone.

embed : Gen n → Word (Gen (₁₊ n))
embed g = [ widen-gen g ]ʷ

------------------------------------------------------------------------
-- The coset action, still to be defined
--
-- h c y pushes the generator y past the blocks of c, returning what
-- escapes onto the lower n wires together with the rewritten blocks.
-- This is §6: y enters on the left of L(n)·M(n) as a dirty gate and is
-- pushed rightwards by the rules of Rewrite, Pushing and PushingZ until
-- it has left the two blocks.
--
-- Two things have to come out in the wash, and neither is settled yet.
-- What escapes must be a word over Gen n, i.e. must not touch the top
-- wire -- that is what Definition 6.1's wire labelling is for, and it
-- will have to be an invariant of the assembled action rather than a
-- remark.  And the assembly is recursive: PushingZ's commZZIIBBBBI
-- emits a controlled-Z one wire up, so pushing through the chain calls
-- itself, and Agda will want that recursion to be structural in the
-- chain.

CosetAction : ℕ → Set
CosetAction n = Coset n → Gen (₁₊ n) → Circuit n × Coset n

------------------------------------------------------------------------
-- The action at the bottom of the tower
--
-- At n = 0 the coset is the whole of a one-qubit normal form's boxes --
-- an A, a C and an E -- and the generators are H, S and the scalar.
-- That is exactly what Rewrite computes, so the base case of h is the
-- one-qubit action with its phase read off.
--
-- Where the phase goes is the point.  Rewrite carries it in the normal
-- form, because at one qubit there is nowhere else for it to be.  In the
-- tower it belongs to the level BELOW: ω is 0-ary, so it is a generator
-- at every width including width 0, and an ω emitted here escapes as
-- part of the Circuit 0 that h returns.  Feeding Rewrite a starting
-- phase of ₀ and reading the result is what converts between the two.
--
-- Circuit 0 is words over Gen 0, and Gen 0 holds only gate₀ -- so the
-- escaping word can be nothing BUT a power of ω, which is why the
-- bottom of the tower is where all the phases end up.  Selinger's (4.5)
-- puts ωᵖ at the end of the normal form for the same reason.

-- The coset and the normal-form body bracket differently -- Coset 0 is
-- Lz 0 × Mx 0 while NFbody 1 is Lz 0 × (Mx 0 × NFbody 0) -- so the two
-- halves are taken apart and put back rather than passed along whole.
-- The trailing tt is NFbody 0, the empty normal form at width 0.
h₀ : CosetAction 0
h₀ (l , m) g with Rw.actGen g ((l , m , tt) , ₀)
... | (l′ , m′ , tt) , p = ω ^ toℕ p , (l′ , m′)
