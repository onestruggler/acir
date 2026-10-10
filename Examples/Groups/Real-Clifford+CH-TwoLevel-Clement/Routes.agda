------------------------------------------------------------------------
-- Presentations of groups
--
-- Routes: the cores of Clément's diagrams (20) and (30) (Diagram20,
-- Diagram30) as routes, and their decorations.
--
-- A decorated route starts with signs Z on indices other than a, then
-- runs the core relabelled, then the letters that undo the signs
-- (Relators.Deco); with flip it ends with the letters that turn
-- Hs a b into Hs b a.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Routes where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat.Base as ℕ using (ℕ)
open import Relation.Nullary using (yes ; no)

open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check using (Let ; Hˡ ; Xˡ ; Zˡ ; Route)

------------------------------------------------------------------------
-- The cores (application order)

private
  f0 f1 f2 f3 f4 f5 : ∀ {m} → Fin (6 ℕ.+ m)
  f0 = zero
  f1 = suc zero
  f2 = suc (suc zero)
  f3 = suc (suc (suc zero))
  f4 = suc (suc (suc (suc zero)))
  f5 = suc (suc (suc (suc (suc zero))))

  g0 g1 g2 g3 : Fin 4
  g0 = zero
  g1 = suc zero
  g2 = suc (suc zero)
  g3 = suc (suc (suc zero))

diag30 : Route 6
diag30 = Hˡ f0 f2 ∷ Hˡ f1 f3 ∷ Hˡ f0 f4 ∷ Hˡ f1 f5 ∷ Hˡ f0 f1 ∷ Zˡ f0 ∷ Zˡ f1 ∷ Hˡ f1 f5 ∷ Hˡ f0 f4 ∷ Hˡ f1 f3 ∷ Hˡ f0 f2 ∷ Hˡ f0 f1 ∷ Hˡ f0 f2 ∷ Hˡ f1 f3 ∷ Hˡ f0 f4 ∷ Hˡ f1 f5 ∷ Zˡ f1 ∷ Zˡ f0 ∷ Hˡ f0 f1 ∷ Hˡ f1 f5 ∷ Hˡ f0 f4 ∷ Hˡ f1 f3 ∷ Hˡ f0 f2 ∷ []

diag20 : Route 4
diag20 = Hˡ g0 g2 ∷ Hˡ g1 g3 ∷ Hˡ g0 g1 ∷ Zˡ g0 ∷ Zˡ g1 ∷ Hˡ g1 g3 ∷ Hˡ g0 g2 ∷ Hˡ g0 g1 ∷ Hˡ g0 g2 ∷ Hˡ g1 g3 ∷ Zˡ g1 ∷ Zˡ g0 ∷ Hˡ g0 g1 ∷ Hˡ g1 g3 ∷ Hˡ g0 g2 ∷ []

------------------------------------------------------------------------
-- Relabelling

-- Relabelling the indices of a route.
relabelL : ∀ {m m′} → (Fin m → Fin m′) → Let m → Let m′
relabelL f (Hˡ i j) = Hˡ (f i) (f j)
relabelL f (Xˡ i j) = Xˡ (f i) (f j)
relabelL f (Zˡ i) = Zˡ (f i)

relabelR : ∀ {m m′} → (Fin m → Fin m′) → Route m → Route m′
relabelR f = map (relabelL f)

------------------------------------------------------------------------
-- Decorations

-- The letter that undoes a sign Z at l after the core H a b.
undo : ∀ {m} (a b l : Fin m) → Let m
undo a b l with l FinP.≟ b
... | yes _ = Xˡ a b
... | no _ = Zˡ l

signs : ∀ {m} → List (Fin m) → Route m
signs = map Zˡ

closing : ∀ {m} (a b : Fin m) → List (Fin m) → Route m
closing a b [] = []
closing a b (l ∷ Q) = closing a b Q ++ (undo a b l ∷ [])

-- Signs, then the core, then the letters that undo the signs.
decorate : ∀ {m} (a b : Fin m) (Q : List (Fin m)) (core : Route m) → Route m
decorate a b Q core = signs Q ++ (core ++ closing a b Q)

-- With the indices of the core H exchanged, the letters that turn
-- Hs a b into Hs b a.
flipped : ∀ {m} (a b : Fin m) → Route m
flipped a b = Zˡ b ∷ Xˡ a b ∷ []

-- The decorated route of a core.
decoRoute : ∀ {k m} → Route (ℕ.suc (ℕ.suc k)) → (Fin (ℕ.suc (ℕ.suc k)) → Fin m) → List (Fin m) → Bool → Route m
decoRoute core lab Q false = decorate (lab zero) (lab (suc zero)) Q (relabelR lab core)
decoRoute core lab Q true = decoRoute core lab Q false ++ flipped (lab zero) (lab (suc zero))

