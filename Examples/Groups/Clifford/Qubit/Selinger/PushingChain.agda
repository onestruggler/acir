------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalization (arXiv:1310.6813, §6): traversing the Z-normal chain.
--
-- The chain runs the opposite way round from the staircase, and that
-- decides everything about this module.  M(n) puts its bottom box
-- FIRST, so dirt entering from the left meets the bottom of the
-- staircase and works upwards.  L(n) puts its bottom box LAST --
-- Normal's [ inj₂ (b , rest) ]ᶜʰ is [ rest ]ᶜʰ ↑ • [ b ]ᴮ -- so dirt
-- meets the TOP of the chain first and works down.
--
-- A gate on the un-shifted wire is therefore the easy case, not the
-- hard one: everything above it in the chain sits on higher wires, so
-- it commutes past the whole of them and arrives at the bottom box with
-- nothing having happened.  No recursion, and the rule that fires is
-- decided by the chain's bottom layer alone:
--
--   a bare A         commHA / commSA   (Rewrite.pushA)
--   a B, A above     commHIB / commSIB (Pushing.pushHB, pushS₀B)
--
-- and the second does not look at what is above the B at all.
--
-- Gates on higher wires are the recursive case and are not here.  Nor
-- is the controlled-Z: even on (0,1) it touches wire 1, which belongs to
-- whatever stands above the bottom box, so it never has this shape --
-- it is always one of PushingZ's two-box rules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.PushingChain
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.List using (List ; map)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import ForStdlib.Data.Fin.Mod using (ℤ)
open import Notations using (₁₊)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Normal p-2 p-prime
  using (Chain)
open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using (Dirty ; S₀ ; X₀ ; pushHB ; pushS₀B)
-- dS belongs to both DirtA and DirtC in Rewrite -- the two alphabets
-- share a name for the S gate -- so it is imported once and left
-- overloaded; Agda picks the right one from the expected type at each
-- use, which is what that feature is for.
open import Examples.Groups.Clifford.Qubit.Selinger.Placed p-2 p-prime
  using (Placed ; places)
open import Examples.Groups.Clifford.Qubit.Selinger.PushingZ p-2 p-prime
  using (Top ; pushZZ-A ; pushZZ-AB ; pushZZ-BB)
open import Examples.Groups.Clifford.Qubit.Selinger.Rewrite p-2 p-prime
  using (DirtA ; dH ; dS ; DirtC ; dX ; pushA)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The A rules speak a narrower alphabet
--
-- Rewrite states commHA and commSA at one qubit, where the only dirt an
-- A box can emit is an X or an S on the single wire.  Those are the
-- same rules at any width -- the A box is a one-qubit gate -- so they
-- are reused rather than restated, with their two-constructor alphabet
-- carried across to the wider one.

fromDirtC : DirtC → Dirty
fromDirtC dX = X₀
fromDirtC dS = S₀

------------------------------------------------------------------------
-- An H or an S on the un-shifted wire
--
-- Straight to the bottom of the chain.  The A case is commHA/commSA and
-- the B case commHIB/commSIB, and in the B case the rest of the chain
-- is returned untouched, which is the whole content of "it commutes
-- past".

push₀-Chain : DirtA → Chain n → ℤ 8 × Chain n × List Dirty
push₀-Chain {0}     d  a with pushA d a
... | k , a′ , o = k , a′ , map fromDirtC o
push₀-Chain {₁₊ n} d  (inj₁ a) with pushA d a
... | k , a′ , o = k , inj₁ a′ , map fromDirtC o
push₀-Chain {₁₊ n} dH (inj₂ (b , r)) with pushHB b
... | k , b′ , o = k , inj₂ (b′ , r) , o
push₀-Chain {₁₊ n} dS (inj₂ (b , r)) with pushS₀B b
... | k , b′ , o = k , inj₂ (b′ , r) , o

------------------------------------------------------------------------
-- Putting an A box back into a chain
--
-- A chain of no B boxes is just the A -- Chain 0 is ABox, not a sum --
-- so at the bottom of the recursion the A is bare and higher up it is
-- inj₁.  chainA is that one-line difference, and it is needed because
-- the controlled-Z rules can CHANGE the number of B boxes and so have
-- to rebuild the chain rather than patch it.

chainA : ∀ n → ABox → Chain n
chainA 0       a = a
chainA (₁₊ n) a = inj₁ a

-- PushingZ returns the chain's top two layers as a sum: either the A
-- alone, or a B with the A above it.  Reading that back as a chain is
-- where a rule that grew or shrank the chain takes effect.
top→chain : Top → Chain (₁₊ n)
top→chain          (inj₁ a)       = inj₁ a
top→chain {n} (inj₂ (b , a)) = inj₂ (b , chainA n a)

------------------------------------------------------------------------
-- A controlled-Z on the un-shifted pair
--
-- This is the one gate that never has the simple shape: on (0,1) it
-- spans the bottom box AND reaches the layer above, so it consumes two
-- layers at once.  Which of PushingZ's three families fires is decided
-- by the chain's first two layers, exactly as verified there:
--
--   a bare A                    commZZAI       and the chain may GROW
--   a B with the A above it     commZZIABB     and it may SHRINK
--   a B with another B above    commZZIIBBBBI  and it keeps its length
--
-- The middle case appears twice below because a chain of exactly one B
-- box stores its A bare (Chain 0 is ABox), while a longer one stores it
-- as inj₁ -- the same configuration written two ways.

pushZZ₀-Chain : Chain (₁₊ n) → ℤ 8 × Chain (₁₊ n) × List Placed
pushZZ₀-Chain (inj₁ a) with pushZZ-A a
... | k , t , o = k , top→chain t , places 0 o
pushZZ₀-Chain {0} (inj₂ (b , a)) with pushZZ-AB a b
... | k , t , o = k , top→chain t , places 0 o
pushZZ₀-Chain {₁₊ n} (inj₂ (b , inj₁ a)) with pushZZ-AB a b
... | k , t , o = k , top→chain t , places 0 o
pushZZ₀-Chain {₁₊ n} (inj₂ (b , inj₂ (b′ , r))) with pushZZ-BB b′ b
... | k , (bu , bl) , o = k , inj₂ (bl , inj₂ (bu , r)) , places 0 o
