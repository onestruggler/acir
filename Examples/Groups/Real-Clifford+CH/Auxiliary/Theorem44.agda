------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 4.4 as the paper states it, and the forms the completeness
-- argument uses (Clément, Section 4.1 and Proposition 4.8)
--
-- The paper's Theorem 4.4, quoted from [Fang, Heunen and Kaarsgaard]:
-- two words over G_N — proper words — with the same matrix are equal
-- modulo Figure 6.  It is the one result the paper imports, and is
-- stated here at the two semantics the development reads auxiliary
-- words in: on four basis vectors (two qubits, TwoQubit) and on 2ⁿ for
-- n = 3 + k (the width of P, Auxiliary.Theorem410Proof).  The
-- completeness argument uses Figure 7 instead, which Proposition 4.8
-- (Auxiliary.LemmaA1) derives from it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem44 where

open import Data.Nat using (ℕ)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LemmaA1 using (Complete⁶ ; proposition-4-8)

import Examples.Groups.Real-Clifford+CH.TwoQubit as TwoQubit
import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410Proof as T410

-- Theorem 4.4 on four basis vectors.
Theorem-4-4₂ : Set
Theorem-4-4₂ = Complete⁶ TwoQubit.BF.⟦_⟧Y _~_

-- Theorem 4.4 on 2ⁿ basis vectors, n = 3 + k.
Theorem-4-4ₙ : ℕ → Set
Theorem-4-4ₙ k = Complete⁶ (T410.BG.⟦_⟧Y k) _~_

-- With Proposition 4.8: Figure 7 is complete for the same words.
figure-7₂ : Theorem-4-4₂ → TwoQubit.Theorem-4-4
figure-7₂ = proposition-4-8 TwoQubit.BF.⟦_⟧Y _~_

figure-7ₙ : ∀ k → Theorem-4-4ₙ k → T410.Theorem-4-4 k
figure-7ₙ k = proposition-4-8 (T410.BG.⟦_⟧Y k) _~_
