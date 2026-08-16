{-# OPTIONS_GHC -w #-}

------------------------------------------------------------------------
-- Circuit figures for the QPL'26 slides (qpl26slides/talk.lagda.tex).
--
-- Reading convention (same as v1rels.hs and the paper): diagrams are
-- read in MATRIX-MULTIPLICATION order -- the rightmost gate is applied
-- first -- so each diagram transcribes its Agda word letter for letter,
-- left to right.  Wires are numbered from the BOTTOM: w sits on wire 0,
-- w ↑ on wire 1, and w ↓ is w itself.
--
-- Emits one .tikz per figure into ../qpl26slides/latex/figures/.
-- Run from the Cir2Tikz root:  runghc -isrc src/qpl26.hs
------------------------------------------------------------------------

import Prelude hiding (Right, Left)
import Data.List (intercalate)
import System.Directory (createDirectoryIfMissing)

import NewBoxRel (Cir (Cir), Rel (Rel), Spec (Spec), rel_trans, cir_trans,
                  UserGate (H, He, S, Se, Z, Ze, X, Xe, CX, CXe, CZ, CZe,
                            A, B, D, E, Mul, I, Sep, Ex))
import qualified Cir2Tikz as CT

------------------------------------------------------------------------
-- Derived words, as gate lists parameterised by the wire they sit on
------------------------------------------------------------------------

sInv :: Int -> UserGate
sInv k = Se k "p-1"

-- Z = H • H • S • H • H • S⁻¹
wZ :: Int -> [UserGate]
wZ k = [H k, H k, S k, H k, H k, sInv k]

-- X = H • S • H • H • S⁻¹ • H
wX :: Int -> [UserGate]
wX k = [H k, S k, H k, H k, sInv k, H k]

-- R = S • Z^½
wR :: Int -> [UserGate]
wR k = [S k, Ze k "1/2"]

-- Ex = CZ • H↓ • H↑ • CZ • H↓ • H↑ • CZ • H↓ • H↑   (on wires k, k+1)
wEx :: Int -> [UserGate]
wEx k = concat (replicate 3 [CZ k (k+1), H k, H (k+1)])

-- ₕ|ₕ = H↓ • CZ • H↓   and   ʰ|ʰ = H↑ • CZ • H↑   on the pair (k, k+1)
hLo, hHi :: Int -> [UserGate]
hLo k = [H k,     CZ k (k+1), H k]
hHi k = [H (k+1), CZ k (k+1), H (k+1)]

-- ⊥⊤ = ₕ|ₕ • ʰ|ʰ   and   ⊤⊥ = ʰ|ʰ • ₕ|ₕ
botTop, topBot :: Int -> [UserGate]
botTop k = hLo k ++ hHi k
topBot k = hHi k ++ hLo k

-- The empty word on n wires.
eps :: Int -> [UserGate]
eps n = map I [0 .. n-1]

box :: Int -> String -> UserGate
box = Mul

------------------------------------------------------------------------
-- Items
------------------------------------------------------------------------

data Item = R String [UserGate] [UserGate] String     -- relation, lhs = rhs
          | C String [UserGate] String                -- single circuit
          | Raw String String                         -- hand-written tikz

items :: [Item]
items =
  ------------------------------------------------------------------
  -- Derived gates (definitions)
  [ R "def-Z"  [Mul 0 "Z"]  (wZ 0) ""
  , R "def-X"  [Mul 0 "X"]  (wX 0) ""
  , R "def-R"  [Mul 0 "R"]  (wR 0) ""
  , R "def-M"  [Mul 0 "M_x"]
               [box 0 "R^{x}", H 0, box 0 "R^{x^{-1}}", H 0, box 0 "R^{x}", H 0]
               ""
  , R "def-Ex" [Ex 0]       (wEx 0) ""
  , R "def-CX" [CX 1 0]     [He 0 "3", CZ 0 1, H 0] ""
  , R "def-XC" [CX 0 1]     [He 1 "3", CZ 0 1, H 1] ""

  ------------------------------------------------------------------
  -- The 16 Paper-V0 Clifford relations (mod scalars)
  -- one-wire
  , R "pv0-order-S"     [Se 0 "p"]                        (eps 1) ""
  , R "pv0-order-H"     [H 0, H 0]                        [Mul 0 "M_{-1}"] ""
  , R "pv0-M-power"     [Mul 0 "(M_g)^{k}"]               [Mul 0 "M_{g^k}"] ""
  , R "pv0-semi-MR"     [Mul 0 "M_g", box 0 "R^{g^2}"]    [Mul 0 "R", Mul 0 "M_g"] ""
  , R "pv0-order-SH"    [S 0, H 0, S 0, H 0, S 0, H 0]    (eps 1) ""
  , R "pv0-comm-HHSHHS" [H 0, H 0, S 0, H 0, H 0, S 0]    [S 0, H 0, H 0, S 0, H 0, H 0] ""
  -- two-wire
  , R "pv0-order-CZ"    [CZe 0 1 "p"]                     (eps 2) ""
  , R "pv0-order-Ex"    [Ex 0, Ex 0]                      (eps 2) ""
  , R "pv0-comm-CZ-Sup" [CZ 0 1, S 1]                     [S 1, CZ 0 1] ""
  , R "pv0-semi-Mup-CZ" [Mul 1 "M_g", CZe 0 1 "g"]        [CZ 0 1, Mul 1 "M_g"] ""
  , R "pv0-semi-Ex-Sup" [Ex 0, S 1]                       [S 0, Ex 0] ""
  , R "pv0-semi-Ex-Hup" [Ex 0, H 1]                       [H 0, Ex 0] ""
  , R "pv0-blake-c12"   [sInv 1, sInv 0, CXe 1 0 "p-1", S 0, CX 1 0]
                        [CZ 0 1] ""
  -- three-wire
  , R "pv0-yang-baxter" [Ex 1, Ex 0, Ex 1]                [Ex 0, Ex 1, Ex 0] ""
  , R "pv0-cz-slide"    [Ex 0, Ex 1, CZ 0 1]              [CZ 1 2, Ex 0, Ex 1] ""
  , R "pv0-semi-CXup-CZdn" [CZ 0 1, CX 2 1]               [CZ 0 2, CX 2 1, CZ 0 1] ""

  ------------------------------------------------------------------
  -- The simplified symplectic relations (Simplified.Syntactics)
  , R "simp-order-S"      [Se 0 "p"]                      (eps 1) ""
  , R "simp-order-H"      [H 0, H 0]                      [Mul 0 "M_{-1}"] ""
  , R "simp-M-power"      [Mul 0 "(M_g)^{k}"]             [Mul 0 "M_{g^k}"] ""
  , R "simp-semi-MS"      [Mul 0 "M_g", S 0]              [Se 0 "g^2", Mul 0 "M_g"] ""
  , R "simp-semi-Mup-CZ"  [Mul 1 "M_g", CZ 0 1]           [CZe 0 1 "g", Mul 1 "M_g"] ""
  , R "simp-semi-Mdn-CZ"  [Mul 0 "M_g", CZ 0 1]           [CZe 0 1 "g", Mul 0 "M_g"] ""
  , R "simp-order-CZ"     [CZe 0 1 "p"]                   (eps 2) ""
  , R "simp-comm-CZ-Sdn"  [CZ 0 1, S 0]                   [S 0, CZ 0 1] ""
  , R "simp-comm-CZ-Sup"  [CZ 0 1, S 1]                   [S 1, CZ 0 1] ""
  , R "simp-selinger-c10" [CZ 0 1, H 1, CZ 0 1]
                          [sInv 1, H 1, sInv 1, CZ 0 1, H 1, sInv 1, sInv 0] ""
  , R "simp-selinger-c11" [CZ 0 1, H 0, CZ 0 1]
                          [sInv 0, H 0, sInv 0, CZ 0 1, H 0, sInv 0, sInv 1] ""
  , R "simp-selinger-c12" [CZ 1 2, CZ 0 1]                [CZ 0 1, CZ 1 2] ""
  , R "simp-selinger-c13" (topBot 1 ++ [CZ 0 1] ++ botTop 1)
                          (botTop 0 ++ [CZ 1 2] ++ topBot 0) ""
  , R "simp-selinger-c14" (concat (replicate 3 (topBot 1 ++ [CZ 0 1])))
                          (eps 3) ""
  , R "simp-selinger-c15" (concat (replicate 3 (botTop 0 ++ [CZ 1 2])))
                          (eps 3) ""

  ------------------------------------------------------------------
  -- Structural rules (Circuit.Base.Lift-Relation)
  , R "str-comm-H"  [Mul 1 "U", H 0]      [H 0, Mul 1 "U"]  ""
  , R "str-comm-CZ" [Mul 2 "U", CZ 0 1]   [CZ 0 1, Mul 2 "U"] ""

  ------------------------------------------------------------------
  -- The Pauli relations (ProjectivePauli.Presentation-Alt)
  , R "pl-order-X"  [Xe 0 "p"]  (eps 1) ""
  , R "pl-order-Z"  [Ze 0 "p"]  (eps 1) ""
  , R "pl-comm-ZX"  [Z 0, X 0]  [X 0, Z 0] ""

  ------------------------------------------------------------------
  -- Scalar correction: order-SH in the exact (with-scalars) rule set
  , R "sc-order-SH" [S 0, H 0, S 0, H 0, S 0, H 0]
                    [Mul 0 "\\omega^{(p^2-1)/8}\\,I"] ""

  ------------------------------------------------------------------
  -- M-mul, the derived multiplier law
  , R "mm-stmt"     [Mul 0 "M_x", Mul 0 "M_y"]  [Mul 0 "M_{xy}"] ""

  ------------------------------------------------------------------
  -- The example word CZ • H ↑ • S on two wires
  , C "ex-word" [CZ 0 1, H 1, S 0] ""

  ------------------------------------------------------------------
  -- S₃: all six elements, as swap circuits
  , C "s3-e"    (eps 3) ""
  , C "s3-s0"   [Ex 0, I 2] ""
  , C "s3-s1"   [Ex 1, I 0] ""
  , C "s3-s01"  [Ex 0, Ex 1] ""
  , C "s3-s10"  [Ex 1, Ex 0] ""
  , C "s3-s010" [Ex 0, Ex 1, Ex 0] ""

  -- The three coset representatives of S₃ / S₂ (staircases)
  , C "c2-0" (eps 3) ""
  , C "c2-1" [Ex 0, I 2] ""
  , C "c2-2" [Ex 0, Ex 1] ""

  -- The two coset representatives of S₂ / S₁
  , C "c1-0" (eps 2) ""
  , C "c1-1" [Ex 0] ""

  ------------------------------------------------------------------
  -- The four cases of pushing a generator through a coset rep
  -- (expanded staircase form, verified permutation identities)
  , R "push-commute" [Ex 0, I 3, Sep, Ex 2]     [Ex 2, Sep, Ex 0, I 3]
      ""
  , R "push-pass"    [Ex 0, Ex 1, Sep, Ex 0]    [Ex 1, Sep, Ex 0, Ex 1]
      ""
  , R "push-absorb"  [Ex 0, Ex 1, Sep, Ex 1]    [Ex 0, I 2]
      ""
  , R "push-extend"  [Ex 0, Sep, Ex 1]          [Ex 0, Ex 1]
      ""

  ------------------------------------------------------------------
  -- The A, B, D, E boxes as circuits (representative a ≠ 0 cases)
  , R "box-A" [A 0 "a,b"] [Mul 0 "M_{a^{-1}}", H 0, Se 0 "-b/a"] ""
  , R "box-B" [B 0 "a,b"] [Ex 0, CXe 1 0 "a", H 1, Se 1 "-b/a"] ""
  , R "box-D" [D 0 "a,b"] [Ex 0, CZe 0 1 "-a", H 0, Se 0 "-b/a"] ""
  , R "box-E" [E 0 "b"]   [Se 0 "-b"] ""
  ]

------------------------------------------------------------------------
-- Hand-written figures: NF staircase, ML decomposition, ML towers
------------------------------------------------------------------------

-- A box spanning wires w..w+k-1 (wire spacing 2), centred at column x.
-- Drawn as a coordinate rectangle so it scales with the picture.
spanBox :: String -> Float -> Int -> Int -> String -> String
spanBox name x w k lbl =
  "\\draw [fill=white] (" ++ show (x - 1.0) ++ ", " ++ show (y0 - 0.75)
  ++ ") rectangle (" ++ show (x + 1.0) ++ ", " ++ show (y1 + 0.75) ++ ");\n"
  ++ "\\node [style=none] (" ++ name ++ ") at (" ++ show x ++ ", "
  ++ show ((y0 + y1) / 2) ++ ") {\\scriptsize $" ++ lbl ++ "$};\n"
  where
    y0, y1 :: Float
    y0 = fromIntegral (2 * w)
    y1 = fromIntegral (2 * (w + k - 1))

wire :: String -> Float -> Float -> Int -> String
wire name x0 x1 w =
  "\\node [style=none] (" ++ name ++ "l) at (" ++ show x0 ++ ", " ++ show y ++ "){};\n"
  ++ "\\node [style=none] (" ++ name ++ "r) at (" ++ show x1 ++ ", " ++ show y ++ "){};\n"
  where y = fromIntegral (2 * w) :: Float

wireDraw :: String -> String
wireDraw name = "\\draw (" ++ name ++ "l.center) to (" ++ name ++ "r.center);\n"

handPicture :: (Float, Float, Float, Float) -> String -> String -> String
handPicture (x0, y0, x1, y1) nodes edges =
  "\\begin{tikzpicture}\n"
  ++ "\\path [use as bounding box] (" ++ show x0 ++ ", " ++ show y0
  ++ ") rectangle (" ++ show x1 ++ ", " ++ show y1 ++ ");\n"
  ++ "\\begin{pgfonlayer}{nodelayer}\n" ++ nodes ++ "\\end{pgfonlayer}\n"
  ++ "\\begin{pgfonlayer}{edgelayer}\n" ++ edges ++ "\\end{pgfonlayer}\n"
  ++ "\\end{tikzpicture}\n"

-- NF 4 = (ML₁ ↑↑↑) • (ML₂ ↑↑) • (ML₃ ↑) • ML₄ : the staircase.
nf4 :: String
nf4 = handPicture (-0.8, -1.0, 9.6, 7.7) nodes edges
  where
    nodes = concat [ wire ("w" ++ show w) (-0.5) 9.3 w | w <- [0..3] ]
         ++ spanBox "ml1" 1.0 3 1 "ML_1"
         ++ spanBox "ml2" 3.3 2 2 "ML_2"
         ++ spanBox "ml3" 5.6 1 3 "ML_3"
         ++ spanBox "ml4" 7.9 0 4 "ML_4"
    edges = concat [ wireDraw ("w" ++ show w) | w <- [0..3] ]

-- ML₄ tower: ML₄ is either M₄ · L₄' or D · (ML₃ ↑).
mlTower :: String
mlTower = handPicture (-0.8, -1.2, 18.8, 7.7) nodes edges
  where
    nodes = concat [ wire ("w" ++ show w) (-0.5) 7.6 w | w <- [0..3] ]
         ++ spanBox "ml4" 1.0 0 4 "ML_4"
         ++ "\\node [style=none] (eq1) at (2.6, 3.0) {\\scriptsize $\\equiv$};\n"
         ++ spanBox "m4" 4.2 0 4 "M_4"
         ++ spanBox "l4" 6.4 0 4 "L_4'"
         ++ "\\node [style=none] (orr) at (8.7, 3.0) {\\scriptsize or};\n"
         ++ concat [ wire ("v" ++ show w) 9.8 18.5 w | w <- [0..3] ]
         ++ spanBox "ml4b" 11.3 0 4 "ML_4"
         ++ "\\node [style=none] (eq2) at (12.9, 3.0) {\\scriptsize $\\equiv$};\n"
         ++ spanBox "d0" 14.5 0 2 "D"
         ++ spanBox "ml3" 16.9 1 3 "ML_3"
    edges = concat [ wireDraw ("w" ++ show w) | w <- [0..3] ]
         ++ concat [ wireDraw ("v" ++ show w) | w <- [0..3] ]

-- M₄ and L₄' unfolded into atomic boxes: M₄ = D•(D↑)•(E↑↑) wait, M 4 on
-- 4 wires: D(0,1) D(1,2) D(2,3) E(3); L₄' = B(2,3) B(1,2) B(0,1) A(0).
mlAtoms :: String
mlAtoms = handPicture (-0.8, -1.2, 16.2, 7.7) nodes edges
  where
    nodes = concat [ wire ("w" ++ show w) (-0.5) 7.4 w | w <- [0..3] ]
         ++ spanBox "m4" 0.7 0 4 "M_4"
         ++ "\\node [style=none] (eq1) at (1.9, 3.0) {$\\equiv$};\n"
         ++ spanBox "d1" 3.0 0 2 "D"
         ++ spanBox "d2" 4.2 1 2 "D"
         ++ spanBox "d3" 5.4 2 2 "D"
         ++ spanBox "e1" 6.6 3 1 "E"
         ++ "\\node [style=none] (blank) at (8.4, 3.0) {};\n"
         ++ concat [ wire ("v" ++ show w) 9.0 16.0 w | w <- [0..3] ]
         ++ spanBox "l4" 10.2 0 4 "L_4'"
         ++ "\\node [style=none] (eq2) at (11.4, 3.0) {$\\equiv$};\n"
         ++ spanBox "b3" 12.5 2 2 "B"
         ++ spanBox "b2" 13.7 1 2 "B"
         ++ spanBox "b1" 14.9 0 2 "B"
         ++ spanBox "a1" 15.7 0 1 "A"
    edges = concat [ wireDraw ("w" ++ show w) | w <- [0..3] ]
         ++ concat [ wireDraw ("v" ++ show w) | w <- [0..3] ]

-- Generic staircase NF for Sₙ (the S₄ instance): c⁽¹⁾ ↑↑ • c⁽²⁾ ↑ • c⁽³⁾.
snStair :: String
snStair = handPicture (-0.8, -1.0, 8.4, 7.7) nodes edges
  where
    nodes = concat [ wire ("w" ++ show w) (-0.5) 8.1 w | w <- [0..3] ]
         ++ spanBox "c1" 1.0 2 2 "c^{(1)}"
         ++ spanBox "c2" 3.3 1 3 "c^{(2)}"
         ++ spanBox "c3" 5.9 0 4 "c^{(3)}"
    edges = concat [ wireDraw ("w" ++ show w) | w <- [0..3] ]

handItems :: [(String, String)]
handItems =
  [ ("nf4",      nf4)
  , ("ml-tower", mlTower)
  , ("sn-stair", snStair)
  ]

------------------------------------------------------------------------
-- Emission (bounding-box hack as in v1rels.hs)
------------------------------------------------------------------------

bboxR :: CT.Relation -> (Float, Float, Float, Float)
bboxR r@(CT.Rel _ c1 c2 _) = (-0.3, ymin, CT.width_of_rel r + 0.3, ymax)
  where
    ws   = CT.wires_of_cir c1 ++ CT.wires_of_cir c2
    ymin = fromIntegral (minimum ws) * 2 - 1.0
    ymax = fromIntegral (maximum ws) * 2 + 1.7

bboxC :: CT.Circuit -> (Float, Float, Float, Float)
bboxC c = (-0.3, ymin, CT.width_of_cir c + 0.3, ymax)
  where
    ws   = CT.wires_of_cir c
    ymin = fromIntegral (minimum ws) * 2 - 1.0
    ymax = fromIntegral (maximum ws) * 2 + 1.7

withBBox :: (Float, Float, Float, Float) -> String -> String
withBBox (x0, y0, x1, y1) body = unlines (h : bb : t)
  where
    (h : t) = lines body
    bb = "\\path [use as bounding box] (" ++ show x0 ++ ", " ++ show y0
         ++ ") rectangle (" ++ show x1 ++ ", " ++ show y1 ++ ");"

-- A relation item also yields its two sides as standalone pictures
-- (NAME-l, NAME-r), so a table can align the ≡ column across rows.
tikzOf :: Item -> [(String, String)]
tikzOf (R nm l r sp) =
  [ (nm, withBBox (bboxR rl) (CT.tikz_of_rel rl))
  , (nm ++ "-l", side l)
  , (nm ++ "-r", side r)
  ]
  where
    rl = rel_trans (Rel CT.Def (Cir l (Spec "")) (Cir r (Spec "")) (Spec sp))
    side gs = let c = cir_trans (Cir gs (Spec "")) in
              withBBox (bboxC c) (CT.tikz_of_cir c)
tikzOf (C nm gs sp) = [(nm, withBBox (bboxC c) (CT.tikz_of_cir c))]
  where c = cir_trans (Cir gs (Spec sp))
tikzOf (Raw nm body) = [(nm, body)]

figDir :: FilePath
figDir = "../qpl26slides/latex/figures/"

main :: IO ()
main = do
  createDirectoryIfMissing True figDir
  let outs = concatMap tikzOf items ++ handItems
  mapM_ write outs
  putStrLn ("wrote " ++ show (length outs) ++ " figures to " ++ figDir)
  where
    write (nm, body) = writeFile (figDir ++ nm ++ ".tikz") body
