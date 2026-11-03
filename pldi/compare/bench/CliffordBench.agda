------------------------------------------------------------------------
-- Execution benchmark: the Agda decision procedure for Clifford circuits
--
-- For random circuits w over H, S and CZ on n wires, decides that w and
-- w S⁴ have the same matrix, with the procedure the soundness proof of
-- Examples.Groups.Qubit-Clifford uses: the Gaussian-integer matrix of a
-- circuit (⟦_⟧ᴳ, a product of stored matrices) compared entry by entry
-- (check).  The circuits come from the same linear congruential
-- generator as Lean/Bench/CliffordBench.lean, so both programs decide
-- the same circuits.
--
-- Usage: CliffordBench n L seed reps   (n ≥ 2)
-- prints the number of decisions that hold (reps) and the milliseconds
-- they took, measured with the monotonic clock inside the program.
-- Compile with: agda --compile --ghc-flag=-O2 (this module is not
-- --safe: it binds GHC's monotonic clock).
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

module pldi.compare.bench.CliffordBench where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _%_ ; _/_ ; _∸_)
import Data.Nat.Show as ℕS
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String ; _++_)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Unit.Polymorphic.Base using () renaming (⊤ to ⊤ₚ)
import Agda.Builtin.IO as Prim
open import IO using (IO ; Main ; run ; putStrLn ; _>>=_ ; _>>_ ; pure)
import IO.Base
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import System.Environment using (getArgs)

open import Instances using (Ring ; SemiRing)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Qubit-Clifford.Syntactics
  using (Gate ; ω-gate ; H-gate ; S-gate ; CZ-gate ; Gen ; gate₀ ; gate₁ ; gate₂ ; _↥ ; Circuit)
import Examples.Groups.Qubit-Clifford.Semantics.Interpretation

------------------------------------------------------------------------
-- The trivial ring, which satisfies every equation the semantics asks
-- of its coefficient ring; the Gaussian evaluation does not use it.

instance
  SemiRing⊤ : SemiRing ⊤
  SemiRing⊤ = record
    { _+_ = λ _ _ → tt ; _*_ = λ _ _ → tt ; 0# = tt ; 1# = tt ; fromℕ = λ _ → tt }

  Ring⊤ : Ring ⊤
  Ring⊤ = record { -_ = λ _ → tt }

open Instances using (-_ ; 0# ; 1#) renaming (_+_ to _⊕_ ; _*_ to _⊛_)

isCR⊤ : IsCommutativeRing (_≡_ {A = ⊤}) _⊕_ _⊛_ -_ 0# 1#
isCR⊤ = record
  { isRing = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record { isEquivalence = Eq.isEquivalence ; ∙-cong = λ _ _ → refl }
            ; assoc = λ _ _ _ → refl }
          ; identity = (λ _ → refl) , (λ _ → refl) }
        ; inverse = (λ _ → refl) , (λ _ → refl)
        ; ⁻¹-cong = λ _ → refl }
      ; comm = λ _ _ → refl }
    ; *-cong = λ _ _ → refl
    ; *-assoc = λ _ _ _ → refl
    ; *-identity = (λ _ → refl) , (λ _ → refl)
    ; distrib = (λ _ _ _ → refl) , (λ _ _ _ → refl) }
  ; *-comm = λ _ _ → refl }

module I = Examples.Groups.Qubit-Clifford.Semantics.Interpretation
  {A = ⊤} isCR⊤ tt refl tt refl

------------------------------------------------------------------------
-- Random circuits

-- x ↦ (1103515245 x + 12345) mod 2³¹.
next : ℕ → ℕ
next x = (1103515245 * x + 12345) % 2147483648

-- A one-wire gate on wire k, a two-wire gate on wires k, k + 1.
place1 : (n k : ℕ) → Gate 1 → Gen n
place1 (suc n) zero    g = gate₁ g
place1 (suc n) (suc k) g = place1 n k g ↥
place1 zero    _       g = gate₀ ω-gate

place2 : (n k : ℕ) → Gate 2 → Gen n
place2 (suc (suc n)) zero    g = gate₂ g
place2 (suc n)       (suc k) g = place2 n k g ↥
place2 _             _       g = gate₀ ω-gate

-- The gate drawn from the state x: H, S or CZ by x mod 3, its wire from
-- the next state.  The width is m + 2.
pick : (m : ℕ) → ℕ → ℕ → Gen (suc (suc m))
pick m c y with c % 3
... | 0 = place1 (suc (suc m)) (y % suc (suc m)) H-gate
... | 1 = place1 (suc (suc m)) (y % suc (suc m)) S-gate
... | _ = place2 (suc (suc m)) (y % suc m) CZ-gate

gates : (m L x : ℕ) → Circuit (suc (suc m))
gates m zero    x = ε
gates m (suc L) x = [ pick m (next x) (next (next x)) ]ʷ • gates m L (next (next x))

S⁴ : (m : ℕ) → Circuit (suc (suc m))
S⁴ m = s • (s • (s • s)) where s = [ place1 (suc (suc m)) 0 S-gate ]ʷ

-- Opaque, so that the typechecker never unfolds the decision on
-- symbolic arguments (a `with` on it ran out of 6 GB); compiled code is
-- unaffected.
opaque
  decide : (m L seed : ℕ) → Bool
  decide m L seed =
    I.check 0 I.⟦ gates m L seed ⟧ᴳ I.⟦ gates m L seed • S⁴ m ⟧ᴳ

------------------------------------------------------------------------
-- Main

add : Bool → ℕ → ℕ
add true  k = suc k
add false k = k

count : (m L seed reps : ℕ) → ℕ
count m L seed zero       = 0
count m L seed (suc reps) = add (decide m L (seed + reps)) (count m L seed reps)

-- The monotonic clock in nanoseconds, from GHC's base library (the
-- standard library's System.Clock needs the Haskell package clock).
postulate monoNanos : Prim.IO ℕ
{-# FOREIGN GHC import qualified GHC.Clock #-}
{-# COMPILE GHC monoNanos = fmap toInteger GHC.Clock.getMonotonicTimeNSec #-}

ms : ℕ → ℕ → ℕ
ms t₀ t₁ = (t₁ ∸ t₀) / 1000000

readℕ : String → ℕ
readℕ s with ℕS.readMaybe 10 s
... | just n  = n
... | nothing = 0

main : Main
main = run do
  args ← getArgs
  go args
  where
  go : List String → IO ⊤ₚ
  go (n ∷ L ∷ seed ∷ reps ∷ []) = do
    t₀ ← IO.Base.lift monoNanos
    let k = count (readℕ n ∸ 2) (readℕ L) (readℕ seed) (readℕ reps)
    putStrLn (ℕS.show k)
    t₁ ← IO.Base.lift monoNanos
    putStrLn (ℕS.show (ms t₀ t₁))
  go _ = putStrLn "usage: CliffordBench n L seed reps"
