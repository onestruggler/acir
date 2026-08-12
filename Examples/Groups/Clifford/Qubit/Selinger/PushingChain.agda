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

open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import ForStdlib.Data.Fin.Mod using (ℤ ; _+_ ; ₀)
open import Notations using (₁₊)

open import Examples.Groups.Clifford.Qubit.Selinger.Boxes p-2 p-prime
open import Examples.Groups.Clifford.Qubit.Selinger.Normal p-2 p-prime
  using (Chain)
open import Examples.Groups.Clifford.Qubit.Selinger.Pushing p-2 p-prime
  using (Dirty ; S₀ ; X₀)
-- dS belongs to both DirtA and DirtC in Rewrite -- the two alphabets
-- share a name for the S gate -- so it is imported once and left
-- overloaded; Agda picks the right one from the expected type at each
-- use, which is what that feature is for.
open import Examples.Groups.Clifford.Qubit.Selinger.Placed p-2 p-prime
  using ( Placed ; _at_ ; Kind ; kH ; kS ; kX ; kZZ
        ; places ; lifts ; pushB1 ; pushBs )
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

------------------------------------------------------------------------
-- Any gate, anywhere on the chain
--
-- The recursion runs the way the chain is written: the layers above the
-- bottom box come FIRST in the word, so a gate on a higher wire meets
-- them before it meets the bottom box.  Hence the shape
--
--   descend into the layers above, at one wire lower;
--   lift what comes back out by one wire;
--   push all of that through the bottom box.
--
-- One gate can leave a layer as several, which is why the second step
-- pushes a LIST (pushBs) and not a gate.  The recursion itself is on the
-- chain, which shrinks, so it terminates for the same reason the chain
-- is finite.
--
-- Cases that pass the gate through are those where the box is not on
-- its wire, plus the two with no rule: an X meeting an A box, and an X
-- meeting a B box on the lower wire.  Nothing delivers either.

placesC : ℕ → List DirtC → List Placed
placesC w o = places w (map fromDirtC o)

push-Chain : Placed → Chain n → ℤ 8 × Chain n × List Placed

-- A bare A on the un-shifted wire.
push-Chain {0} (kH at 0)      a with pushA dH a
... | k , a′ , o = k , a′ , placesC 0 o
push-Chain {0} (kS at 0)      a with pushA dS a
... | k , a′ , o = k , a′ , placesC 0 o
push-Chain {0} (kX at 0)      a = ₀ , a , (kX at 0) ∷ []
-- a one-wire chain has no pair for a controlled-Z to span
push-Chain {0} (kZZ at 0)     a = ₀ , a , (kZZ at 0) ∷ []
push-Chain {0} (k at ₁₊ w)   a = ₀ , a , (k at ₁₊ w) ∷ []

-- An A with room above it: the A is still on the un-shifted wire, so
-- only a gate there meets anything.
push-Chain {₁₊ n} (kH at 0)    (inj₁ a) with pushA dH a
... | k , a′ , o = k , inj₁ a′ , placesC 0 o
push-Chain {₁₊ n} (kS at 0)    (inj₁ a) with pushA dS a
... | k , a′ , o = k , inj₁ a′ , placesC 0 o
push-Chain {₁₊ n} (kX at 0)    (inj₁ a) = ₀ , inj₁ a , (kX at 0) ∷ []
push-Chain {₁₊ n} (kZZ at 0)   (inj₁ a) = pushZZ₀-Chain (inj₁ a)
push-Chain {₁₊ n} (k at ₁₊ w) (inj₁ a) = ₀ , inj₁ a , (k at ₁₊ w) ∷ []

-- A B box at the bottom.  On the un-shifted wire the gate reaches it
-- directly; on the pair it spans it, and that is the two-box case.
push-Chain {₁₊ n} (kZZ at 0)   (inj₂ (b , r)) = pushZZ₀-Chain (inj₂ (b , r))
push-Chain {₁₊ n} (kH at 0)    (inj₂ (b , r)) with pushB1 (kH at 0) b
... | k , b′ , o = k , inj₂ (b′ , r) , o
push-Chain {₁₊ n} (kS at 0)    (inj₂ (b , r)) with pushB1 (kS at 0) b
... | k , b′ , o = k , inj₂ (b′ , r) , o
push-Chain {₁₊ n} (kX at 0)    (inj₂ (b , r)) = ₀ , inj₂ (b , r) , (kX at 0) ∷ []
push-Chain {₁₊ n} (k at ₁₊ w) (inj₂ (b , r)) with push-Chain (k at w) r
... | k₁ , r′ , out with pushBs (lifts out) b
...   | k₂ , b′ , out′ = k₁ + k₂ , inj₂ (b′ , r′) , out′
