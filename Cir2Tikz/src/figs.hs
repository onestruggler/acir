{-# OPTIONS_GHC -w #-}

-- Generator for the circuit figures in the paper.  Emits:
--   fig1_sigma.tikz      Fig 1  three permutation circuits, side by side
--   fig2_comm2.tikz      Fig 2a far-commutation (disjoint gates commute)
--   fig2_yb.tikz         Fig 2b Yang-Baxter / braid relation
--   fig3_staircase.tikz  Fig 3  a staircase normal-form section
--
-- Swap gate = Ex k (crosses wires k and k+1).  I k is an idle wire that
-- draws nothing but keeps a wire in range.  Sep is a column barrier.

import Prelude hiding (Right, Left)

import NewBoxRel (Cir (Cir), Spec (Spec), UserGate (Ex, I, Sep), cir_trans)
import qualified Cir2Tikz as CT
import Cir2Tikz (tikz_of_cir, tikz_of_pcir, PositionSpec (PositionSpec),
                 Direction (Up, Down, Right, Left, LU, LD, RU, RD))

------------------------------------------------------------------------
-- Fig 1 : sigma, sigma-up, and the braid word, laid out side by side.
------------------------------------------------------------------------

sigma, sigmaUp, braid :: Cir
sigma   = Cir [Ex 0, I 2] (Spec "$\\sigma$")
sigmaUp = Cir [Ex 1, I 0] (Spec "$\\sigma\\!\\uparrow$")
braid   = Cir [Ex 0, Ex 1, Ex 0]
              (Spec "$\\sigma \\cdot \\sigma\\!\\uparrow \\cdot \\sigma$")

fig1 :: [(CT.Circuit, PositionSpec)]
fig1 =
  [ (cir_trans sigma   , PositionSpec Right "")
  , (cir_trans sigmaUp , PositionSpec Right "")
  , (cir_trans braid   , PositionSpec Right "")
  ]

------------------------------------------------------------------------
-- Fig 2a : far-commutation.  Two swaps on disjoint wire pairs {2,3} and
-- {0,1}.  Sep forces them into separate columns so the two sides read as
-- "top-then-bottom = bottom-then-top"; the trailing I bridges the Sep's
-- wire range across the gap so the barrier actually bites.
------------------------------------------------------------------------

comm2L, comm2R :: Cir
comm2L = Cir [Ex 2, Sep, Ex 0, I 3] (Spec "")
comm2R = Cir [Ex 0, Sep, Ex 2, I 0] (Spec "")

fig2_comm2 :: [(CT.Circuit, PositionSpec)]
fig2_comm2 =
  [ (cir_trans comm2L , PositionSpec Right "=")
  , (cir_trans comm2R , PositionSpec Right "")
  ]

------------------------------------------------------------------------
-- Fig 2b : Yang-Baxter.  sigma.sigma-up.sigma = sigma-up.sigma.sigma-up.
------------------------------------------------------------------------

ybL, ybR :: Cir
ybL = Cir [Ex 0, Ex 1, Ex 0] (Spec "")
ybR = Cir [Ex 1, Ex 0, Ex 1] (Spec "")

fig2_yb :: [(CT.Circuit, PositionSpec)]
fig2_yb =
  [ (cir_trans ybL , PositionSpec Right "=")
  , (cir_trans ybR , PositionSpec Right "")
  ]

------------------------------------------------------------------------
-- Fig 3 : a staircase normal-form section on four wires.
------------------------------------------------------------------------

staircase :: Cir
staircase = Cir [Ex 0, Ex 1, Ex 2, Ex 1] (Spec "")

------------------------------------------------------------------------

-- Pictures land in figures/, which is where \tikzfig looks after failing to
-- find NAME.tikz beside the .tex.  Run from the Cir2Tikz root.
writeFig :: FilePath -> String -> IO ()
writeFig fname = writeFile ("figures/" ++ fname ++ ".tikz")

main :: IO ()
main = do
  writeFig "fig1_sigma"     (tikz_of_pcir fig1)
  writeFig "fig2_comm2"     (tikz_of_pcir fig2_comm2)
  writeFig "fig2_yb"        (tikz_of_pcir fig2_yb)
  writeFig "fig3_staircase" (tikz_of_cir (cir_trans staircase))
