{-# OPTIONS_GHC -w #-}

------------------------------------------------------------------------
-- Circuit figures for the relation set of
--
--   Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
--
-- i.e. the constructors of Clifford-Relations.Base._SRel,_===_, the three
-- structural commutations Clifford-Relations exports, and the derived
-- words those relations are stated over.
--
-- Reading convention (the same as paper/sections/fig-relations.tex):
-- diagrams are read in MATRIX-MULTIPLICATION order -- the rightmost gate
-- is applied first -- so each diagram transcribes its Agda word letter
-- for letter, left to right.  Wires are numbered from the BOTTOM, so w
-- lives on wire 0, w ↑ on wire 1, w ↑ ↑ on wire 2, and w ↓ is w itself.
--
-- Emits one .tikz per relation into figures/v1/, plus the driver v1rels.tex.
-- Run from the Cir2Tikz root:  runghc -isrc src/v1rels.hs
------------------------------------------------------------------------

import Prelude hiding (Right, Left)
import Data.List (intercalate)
import System.Directory (createDirectoryIfMissing)

import NewBoxRel (Cir (Cir), Rel (Rel), Spec (Spec), rel_trans,
                  UserGate (H, He, S, Se, Z, Ze, X, Xe, CZ, CZe, Mul, I, Sep))
import qualified Cir2Tikz as CT

------------------------------------------------------------------------
-- Derived words, as gate lists parameterised by the wire they sit on
------------------------------------------------------------------------

-- S⁻¹ = S ^ p-1 (Symplectic.Syntactics); shown with its true exponent.
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

-- R as a single box, for the relations that only ever use it whole.
box :: Int -> String -> UserGate
box = Mul

-- M x = R^x • H • R^{x⁻¹} • H • R^x • H
wM :: Int -> String -> String -> [UserGate]
wM k x xi = [box k ("R^{" ++ x ++ "}"), H k,
             box k ("R^{" ++ xi ++ "}"), H k,
             box k ("R^{" ++ x ++ "}"), H k]

-- ₕ|ₕ = H ↓ • CZ • H ↓  and  ʰ|ʰ = H ↑ • CZ • H ↑, on the wire pair (k,k+1)
hLo, hHi :: Int -> [UserGate]
hLo k = [H k,       CZ k (k+1), H k]
hHi k = [H (k+1),   CZ k (k+1), H (k+1)]

-- ⊥⊤ = ₕ|ₕ • ʰ|ʰ   and   ⊤⊥ = ʰ|ʰ • ₕ|ₕ
botTop, topBot :: Int -> [UserGate]
botTop k = hLo k ++ hHi k
topBot k = hHi k ++ hLo k

-- The empty word on n wires: idle wires, drawn but occupying no columns.
eps :: Int -> [UserGate]
eps n = map I [0 .. n-1]

------------------------------------------------------------------------
-- The figure
------------------------------------------------------------------------

data Item = Section String | Item String String [UserGate] [UserGate] String

rel :: String -> String -> [UserGate] -> [UserGate] -> String -> Item
rel = Item

items :: [Item]
items =
  [ Section "Derived words (definitions)"

  , rel "def-Z"  "$Z$"
        [Mul 0 "Z"]                       (wZ 0)                          ""
  , rel "def-X"  "$X$"
        [Mul 0 "X"]                       (wX 0)                          ""
  , rel "def-R"  "$R$"
        [Mul 0 "R"]                       (wR 0)                          ""
  , rel "def-M"  "$M_x$"
        [Mul 0 "M_x"]                     (wM 0 "x" "x^{-1}")             "$x \\neq 0$"
  , rel "def-bt" "$\\bot\\top$"
        [Mul 0 "\\bot", Mul 1 "\\top"]    (botTop 0)                      ""
  , rel "def-tb" "$\\top\\bot$"
        [Mul 1 "\\top", Mul 0 "\\bot"]    (topBot 0)                      ""

  , Section "One-wire axioms"

  , rel "order-S" "order-S"
        [Se 0 "p"]                        (eps 1)                         ""
  , rel "order-H" "order-H"
        [H 0, H 0]                        [Mul 0 "M_{-1}"]                ""
  , rel "M-power" "M-power"
        [Mul 0 "(M_g)^{k}"]               [Mul 0 "M_{g^k}"]               ""
  , rel "semi-MR" "semi-MR"
        [Mul 0 "M_g", Mul 0 "R"]          [Mul 0 "R^{g^2}", Mul 0 "M_g"]  ""
  , rel "order-SH" "order-SH"
        [S 0, H 0, S 0, H 0, S 0, H 0]    (eps 1)                         ""
  , rel "comm-HHSHHS" "comm-HHSHHS"
        [H 0, H 0, S 0, H 0, H 0, S 0]    [S 0, H 0, H 0, S 0, H 0, H 0]  ""

  , Section "Two-wire axioms"

  , rel "semi-M-up-CZ" "semi-M\\ensuremath{\\uparrow}CZ"
        [Mul 1 "M_g", CZ 0 1]             [CZe 0 1 "g", Mul 1 "M_g"]      ""
  , rel "semi-M-dn-CZ" "semi-M\\ensuremath{\\downarrow}CZ"
        [Mul 0 "M_g", CZ 0 1]             [CZe 0 1 "g", Mul 0 "M_g"]      ""
  , rel "rel-Xup-CZ" "rel-X\\ensuremath{\\uparrow}-CZ"
        ([CZ 0 1] ++ wX 1)                (wX 1 ++ wZ 0 ++ [CZ 0 1])      ""
  , rel "rel-Xdn-CZ" "rel-X\\ensuremath{\\downarrow}-CZ"
        ([CZ 0 1] ++ wX 0)                (wX 0 ++ wZ 1 ++ [CZ 0 1])      ""
  , rel "order-CZ" "order-CZ"
        [CZe 0 1 "p"]                     (eps 2)                         ""
  , rel "comm-CZ-Sdn" "comm-CZ-S\\ensuremath{\\downarrow}"
        [CZ 0 1, S 0]                     [S 0, CZ 0 1]                   ""
  , rel "comm-CZ-Sup" "comm-CZ-S\\ensuremath{\\uparrow}"
        [CZ 0 1, S 1]                     [S 1, CZ 0 1]                   ""
  , rel "selinger-c10" "selinger-c10"
        [CZ 0 1, H 1, CZ 0 1]
        [box 1 "R^{p-1}", H 1, box 1 "R^{p-1}", CZ 0 1,
         H 1, box 1 "R^{p-1}", box 0 "R^{p-1}"]                           ""
  , rel "selinger-c11" "selinger-c11"
        [CZ 0 1, H 0, CZ 0 1]
        [box 0 "R^{p-1}", H 0, box 0 "R^{p-1}", CZ 0 1,
         H 0, box 0 "R^{p-1}", box 1 "R^{p-1}"]                           ""

  , Section "Three-wire axioms"

  , rel "selinger-c12" "selinger-c12"
        [CZ 1 2, CZ 0 1]                  [CZ 0 1, CZ 1 2]                ""
  , rel "selinger-c13" "selinger-c13"
        (topBot 1 ++ [CZ 0 1] ++ botTop 1)
        (botTop 0 ++ [CZ 1 2] ++ topBot 0)                                ""
  , rel "selinger-c14" "selinger-c14"
        (concat (replicate 3 (topBot 1 ++ [CZ 0 1])))
        (eps 3)                                                           ""
  , rel "selinger-c15" "selinger-c15"
        (concat (replicate 3 (botTop 0 ++ [CZ 1 2])))
        (eps 3)                                                           ""

  , Section "Structural rules (Circuit.Base.Lift-Relation)"

  , rel "comm-H" "comm-H"
        [Mul 1 "U", H 0]                  [H 0, Mul 1 "U"]                ""
  , rel "comm-S" "comm-S"
        [Mul 1 "U", S 0]                  [S 0, Mul 1 "U"]                ""
  , rel "comm-CZ" "comm-CZ"
        [Mul 2 "U", CZ 0 1]               [CZ 0 1, Mul 2 "U"]             ""
  ]

------------------------------------------------------------------------
-- Emission
------------------------------------------------------------------------

-- Everything tikz_of_rel emits sits on the `nodelayer`/`edgelayer` pgf layers,
-- and pgf only grows a picture's bounding box from material on the main layer.
-- The pictures therefore measure as very nearly empty, and consecutive rows of
-- the table collide.  Compute the true extent from Cir2Tikz's own geometry and
-- pin it down with `use as bounding box`.
bbox :: CT.Relation -> (Float, Float, Float, Float)
bbox r@(CT.Rel _ c1 c2 _) = (-0.3, ymin, CT.width_of_rel r + 0.3, ymax)
  where
    ws   = CT.wires_of_cir c1 ++ CT.wires_of_cir c2
    ymin = fromIntegral (minimum ws) * 2 - 1.0   -- half a gate box below
    ymax = fromIntegral (maximum ws) * 2 + 1.7   -- gate box + a `label=above`

tikzOf :: Item -> String
tikzOf (Item _ _ l r sp) = unlines (h : bb : t)
  where
    rl        = rel_trans (Rel CT.Def (Cir l (Spec "")) (Cir r (Spec "")) (Spec sp))
    (h : t)   = lines (CT.tikz_of_rel rl)
    (x0,y0,x1,y1) = bbox rl
    bb = "\\path [use as bounding box] (" ++ show x0 ++ ", " ++ show y0
         ++ ") rectangle (" ++ show x1 ++ ", " ++ show y1 ++ ");"

texBody :: Item -> String
texBody (Section t) =
  "\\multicolumn{2}{@{}l}{\\bfseries " ++ t ++ "}\\\\*[2pt]"
texBody (Item nm cap _ _ _) =
  "{\\footnotesize " ++ cap ++ "} & \\fitfig{v1/" ++ nm ++ "}\\\\[7pt]"

texFile :: String
texFile = unlines $
  [ "% Generated by Cir2Tikz/v1rels.hs -- do not edit by hand."
  , "% Build with:  pdflatex v1rels.tex   (run from the Cir2Tikz directory)"
  , "\\documentclass[11pt]{article}"
  , "\\usepackage[margin=1.4cm,landscape,a4paper]{geometry}"
  , "\\usepackage{amsmath,amssymb,longtable,graphicx}"
  , "\\usepackage{tikzit}"
  , "\\input{circuits.tikzstyles}"
  , "\\definecolor{normGreen}{RGB}{214,243,221}"
  , "\\definecolor{normRed}{RGB}{249,196,196}"
  , "\\definecolor{normYellow}{RGB}{253,246,208}"
  , "\\pagestyle{empty}"
  , "\\setlength{\\LTpre}{0pt}\\setlength{\\LTpost}{0pt}"
  -- longtable breaks at chunk boundaries; the default 20 lands mid-page here.
  , "\\setcounter{LTchunksize}{200}"
  -- Circuits for the three-wire axioms are far wider than the text block, so
  -- shrink a picture to \figwidth if and only if it overflows; and \vcenter it,
  -- so that a multi-wire circuit sits beside the middle of its name rather than
  -- hanging off the baseline that tikzit pins to the bottom wire.
  , "\\newlength{\\figwidth}"
  , "\\newsavebox{\\figbox}"
  , "\\newcommand{\\fitfig}[1]{%"
  , "  \\sbox{\\figbox}{\\tikzfig{#1}}%"
  , "  \\ifdim\\wd\\figbox>\\figwidth"
  , "    \\sbox{\\figbox}{\\resizebox{\\figwidth}{!}{\\usebox{\\figbox}}}%"
  , "  \\fi"
  , "  $\\vcenter{\\hbox{\\usebox{\\figbox}}}$}"
  , "\\begin{document}"
  , "\\setlength{\\figwidth}{\\dimexpr\\textwidth-9em\\relax}"
  , "\\begin{center}"
  , "  {\\Large The relation set of \\texttt{Simplified-V1.Syntactics}}\\\\[2pt]"
  , "  {\\footnotesize \\texttt{Clifford-Relations.Base.\\_SRel,\\_===\\_} together"
  , "   with the structural rules of \\texttt{Circuit.Base.Lift-Relation}.\\\\"
  , "   Diagrams read left to right in matrix-multiplication order (the"
  , "   \\emph{rightmost} gate is applied first), so each transcribes its Agda"
  , "   word letter for letter.  Wires are numbered from the bottom: $w$ sits on"
  , "   wire $0$, $w\\uparrow$ on wire $1$, and $w\\downarrow$ is $w$ itself.}"
  , "\\end{center}"
  , "\\begin{longtable}{@{}r@{\\quad}l@{}}"
  ] ++ map texBody items ++
  [ "\\end{longtable}"
  , "\\end{document}"
  ]

-- Pictures go to figures/v1/; \tikzfig{v1/NAME} finds them through its
-- ./figures/ fallback.  Run from the Cir2Tikz root.
figDir :: FilePath
figDir = "figures/v1/"

main :: IO ()
main = do
  createDirectoryIfMissing True figDir
  mapM_ write items
  writeFile "v1rels.tex" texFile
  putStrLn ("wrote " ++ show (length [() | Item{} <- items])
            ++ " relations to " ++ figDir)
  where
    write s@(Item nm _ _ _ _) = writeFile (figDir ++ nm ++ ".tikz") (tikzOf s)
    write _                   = return ()
