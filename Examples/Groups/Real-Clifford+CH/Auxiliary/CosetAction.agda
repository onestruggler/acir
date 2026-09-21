------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset action of the Reidemeister–Schreier method
-- (Clément, Definition A.2)
--
-- The method's third datum is a function that slides an auxiliary
-- generator past a coset: given a coset c and a generator y, it says
-- which word of P is peeled off and which coset is landed in.  Written
-- as matrices, `act c y = (w , c′)` means
--
--     rep c · y  =  w · rep c′,
--
-- with w in the even-parity subgroup — a word over P.  The table is
-- Definition A.2's, with the paper's two index shorthands read as they
-- are meant: in each branch one of a, b is known to be the index 0 or
-- the index 1, and `a + b` resp. `ab` names *the other one*.
--
-- The two distinguished indices are parameters here, since any two
-- distinct ones will do and `Fin (2 ^ n)` has no literals at a
-- symbolic width.  `z` is the paper's 0 and `o` its 1.
--
-- `Gen` carries no distinctness proof on X[a,b] and H[a,b] while the
-- letters of P do, so the action answers `ε` on a degenerate letter.
-- That is harmless: only the images of P-letters and the two sides of
-- a Figure 7 rule are ever run through it, and those have distinct
-- indices by construction.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ) renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality using (_≢_)

module Examples.Groups.Real-Clifford+CH.Auxiliary.CosetAction
  (n : ℕ) (z o : Fin (2 ^ℕ n)) (z≢o : z ≢ o) where

open import Data.Fin.Properties using (_≟_)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets
  using (Coset ; ⟨ε⟩ ; ⟨M⟩ ; ⟨K⟩ ; ⟨KM⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
  using (GenP ; −1−1 ; −1X ; XX ; HH)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])

private
  N : ℕ
  N = 2 ^ℕ n

  Step : Set
  Step = Word (GenP n) × Coset

  o≢z : o ≢ z
  o≢z e = z≢o (sym e)

------------------------------------------------------------------------
-- Where a pair of indices sits relative to the two distinguished ones

private
  -- `both`: the pair is {z , o}; `hasZ t`: one index is z and the
  -- other, t, is neither z nor o; `hasO t`: one is o and the other, t,
  -- is neither; `none`: the pair misses both.
  data Cls : Set where
    both : Cls
    hasZ : (t : Fin N) → .(t ≢ o) → Cls
    hasO : (t : Fin N) → .(z ≢ t) → Cls
    none : Cls

  cls : Fin N → Fin N → Cls
  cls a b with a ≟ z
  ... | yes _   with b ≟ o
  ...           | yes _    = both
  ...           | no  b≢o  = hasZ b b≢o
  cls a b | no a≢z with b ≟ z
  ...              | yes _   with a ≟ o
  ...                        | yes _   = both
  ...                        | no a≢o  = hasZ a a≢o
  cls a b | no a≢z | no b≢z with a ≟ o
  ...                       | yes _  = hasO b (λ e → b≢z (sym e))
  ...                       | no a≢o with b ≟ o
  ...                                | yes _ = hasO a (λ e → a≢z (sym e))
  ...                                | no  _ = none

------------------------------------------------------------------------
-- The action
--
-- Each clause is one line of Definition A.2's table for h.

act : Coset → G.Gen N → Step

-- rep ⟨ε⟩ = ε.
act ⟨ε⟩ −1[ a ]     = [ −1−1 o a ]ʷ , ⟨M⟩
act ⟨ε⟩ X[ a , b ]  with a ≟ b
... | yes _   = ε , ⟨ε⟩
... | no a≢b  with a ≟ o
...           | yes _ = [ −1X b a b a≢b ]ʷ , ⟨M⟩
...           | no  _ with b ≟ o
...                   | yes _ = [ −1X a a b a≢b ]ʷ , ⟨M⟩
...                   | no  _ = [ −1X o a b a≢b ]ʷ , ⟨M⟩
act ⟨ε⟩ H[ a , b ]  with a ≟ b
... | yes _  = ε , ⟨ε⟩
... | no a≢b = [ HH a b z o a≢b z≢o ]ʷ , ⟨K⟩

-- rep ⟨M⟩ = (−1)_[o].
act ⟨M⟩ −1[ a ]     = [ −1−1 o a ]ʷ , ⟨ε⟩
act ⟨M⟩ X[ a , b ]  with a ≟ b
... | yes _  = ε , ⟨M⟩
... | no a≢b = [ −1X o a b a≢b ]ʷ , ⟨ε⟩
act ⟨M⟩ H[ a , b ]  with a ≟ b
... | yes _  = ε , ⟨M⟩
... | no a≢b with a ≟ o
...          | yes _ = [ −1X b a b a≢b ]ʷ • [ HH a b z o a≢b z≢o ]ʷ , ⟨KM⟩
...          | no  _ with b ≟ o
...                  | yes _ = [ −1X b a b a≢b ]ʷ • [ HH a b z o a≢b z≢o ]ʷ , ⟨KM⟩
...                  | no  _ = [ HH a b z o a≢b z≢o ]ʷ , ⟨KM⟩

-- rep ⟨K⟩ = H_[z,o].
act ⟨K⟩ −1[ a ]     with a ≟ z
... | yes _ = [ −1−1 o a ]ʷ , ⟨KM⟩
... | no  _ with a ≟ o
...         | yes _ = [ −1−1 o a ]ʷ , ⟨KM⟩
...         | no  _ = [ −1X a z o z≢o ]ʷ , ⟨KM⟩
act ⟨K⟩ X[ a , b ]  with a ≟ b
... | yes _  = ε , ⟨K⟩
... | no a≢b with cls a b
...          | both     = [ −1X o z o z≢o ]ʷ , ⟨KM⟩
...          | hasZ t p = [ XX z o a b z≢o a≢b ]ʷ • [ HH t o z o p z≢o ]ʷ , ⟨KM⟩
...          | hasO t p = [ −1X t a b a≢b ]ʷ • [ HH z t z o p z≢o ]ʷ , ⟨KM⟩
...          | none     = [ XX a b z o a≢b z≢o ]ʷ , ⟨KM⟩
act ⟨K⟩ H[ a , b ]  with a ≟ b
... | yes _  = ε , ⟨K⟩
... | no a≢b = [ HH z o a b z≢o a≢b ]ʷ , ⟨ε⟩

-- rep ⟨KM⟩ = H_[z,o] (−1)_[o].
act ⟨KM⟩ −1[ a ]    with a ≟ z
... | yes _ = [ −1−1 o a ]ʷ , ⟨K⟩
... | no  _ with a ≟ o
...         | yes _ = [ −1−1 o a ]ʷ , ⟨K⟩
...         | no  _ = [ −1X a z o z≢o ]ʷ , ⟨K⟩
act ⟨KM⟩ X[ a , b ] with a ≟ b
... | yes _  = ε , ⟨KM⟩
... | no a≢b with cls a b
...          | both     = [ −1X z z o z≢o ]ʷ , ⟨K⟩
...          | hasZ t p = [ XX z o a b z≢o a≢b ]ʷ • [ HH t o z o p z≢o ]ʷ , ⟨K⟩
...          | hasO t p = [ XX z o a b z≢o a≢b ]ʷ • [ HH z t z o p z≢o ]ʷ , ⟨K⟩
...          | none     = [ XX a b z o a≢b z≢o ]ʷ , ⟨K⟩
act ⟨KM⟩ H[ a , b ] with a ≟ b
... | yes _  = ε , ⟨KM⟩
... | no a≢b with a ≟ o
...          | yes _ = [ HH z o a b z≢o a≢b ]ʷ • [ −1X a a b a≢b ]ʷ , ⟨M⟩
...          | no  _ with b ≟ o
...                  | yes _ = [ HH z o a b z≢o a≢b ]ʷ • [ −1X a a b a≢b ]ʷ , ⟨M⟩
...                  | no  _ = [ HH z o a b z≢o a≢b ]ʷ , ⟨M⟩
