------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary A.8: the equations of Figure 10
--
-- Figure 10 is thirteen equations, (65) to (77), over the alphabet P.
-- (65) is the one the others are proved from, and it is a hypothesis
-- here, proved in `Auxiliary/Eq65H` (`eq65-full`).  Over (65), this
-- module re-exports the others, under their equation numbers.
--
--   (66)  `eq66`   H_[a,b] H_[c,d]  ≈  H_[c,d] H_[a,b]        (Figure10)
--   (67)  `eq67`   H_[b,a] H_[c,d]
--                      ≈  (H_[a,b]H_[c,d]) ((−1)_[b]X_[a,b])  (Eq67)
--   (70)  `eq70`   H_[a,b] H_[a,b]  ≈  ε                      (Figure10)
--   (71)  `eq71`   (H_[a,b]H_[c,d])(H_[c,d]H_[e,f])
--                                   ≈  H_[a,b] H_[e,f]        (Fuse)
--   (72)  `eq72`   H_[a,b] H_[b,a]  ≈  (−1)_[b] X_[a,b]         (Eq67)
--   (73)  `eq73`   (H_[a,b]H_[c,d])(H_[e,f]H_[g,h])
--                      ≈  (H_[a,b]H_[e,f])(H_[c,d]H_[g,h])    (Fuse)
--   (74)  `eq74`   a mixed letter away from the pair commutes  (Figure10)
--   (75)  `eq75`   ((−1)_[a]X_[a,b]) (H_[a,b]H_[c,d])
--                      ≈  (H_[a,b]H_[c,d]) ((−1)_[b]X_[a,b])  (Eq75)
--   (76)  `eq76`   ((−1)_[a]X_[a,e]) (H_[a,b]H_[c,d])
--                      ≈  (H_[e,b]H_[c,d]) ((−1)_[a]X_[a,e])  (Move)
--   (77)  `eq77`   ((−1)_[a]X_[a,e]) (H_[e,b]H_[c,d])
--                      ≈  (H_[a,b]H_[c,d]) ((−1)_[a]X_[a,b]) ((−1)_[a]X_[a,e])
--                                                              (Eq77)
--
-- **(68) is (76) at e = a + 1, and (69) is (77) there**, so both are
-- here too; the figure states them separately because only the
-- consecutive ones are needed where they are used.  **So Figure 10 is
-- complete, over (65).**  (67) needed Equation (40): the only word that
-- turns a pair round, its own exchange, signs the pair's two indices
-- unequally, so neither Corollary A.7 nor `hh-conj` reaches it, and (40)
-- — a sign pair crossing the standard pair at the cost of a letter — is
-- exactly the rule that says what happens then.  (75) needed it
-- conjugated onto the first pair by the double exchange (44), and (77)
-- needs it carried to an arbitrary tuple (`Eq77.Frame.std`).

-- Also re-exported is the kit the proofs are built from, which is
-- worth more than the individual equations: a letter squares to ε, a
-- letter and its reverse cancel, and a Hadamard-free word with an
-- inverse passes a pair, renaming its four indices (`hh-pass`, with
-- `xx-pass` its instance at a double exchange — the shape item (b)
-- will meet, the coset action producing one beside a Hadamard letter
-- at three of its four cosets, and `zz-pass` the third shape — a sign
-- pair on the Hadamard pair's own two indices, which is the general
-- form of Equation (39)).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.CorollaryA8 (m : ℕ) where

-- Each of these takes (65) — the module's one hypothesis — as its
-- first argument, the anonymous module it is proved in having turned
-- into a parameter.

-- (65) itself, (66), (70) and (74).
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m public
  using (Eq65 ; eq66 ; eq70 ; eq74)

-- (71), (73), and the kit the degenerate cases are built from.
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Fuse m public
  using (Off ; mkOff ; hh-invol ; hh-cancel ; hub ; fuse-fresh ; eq73)
  renaming (fuse to eq71)

-- (76) — and (68), which is (76) at e = a + 1 — with the general form
-- of the passing lemma behind them.
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Move m public
  using (hh-conj ; hh-pass ; xx-pass ; zz-pass ; eq76)

-- (75), from Equation (40) carried to the first pair by (44).
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq75 m public
  using (eq40′ ; eq75₀ ; eq75)

-- (67), from (40), (75) on the second pair and `hh-conj`; and (72).
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq67 m public
  using (eq67₀ ; eq67 ; eq72)

-- (77), and (40) at any tuple.
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq77 m public
  using (module Frame ; eq77)
