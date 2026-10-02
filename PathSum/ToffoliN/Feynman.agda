------------------------------------------------------------------------
-- Presentations of groups
--
-- The standard n-bit Toffoli decomposition exactly as the paper's tool
-- builds it, gate for gate, for every n (Amy, QPL 2018, section 5.2
-- and table 2)
--
-- The paper's tool, Feynman (github.com/meamy/feynman), builds the
-- circuits it verified as table 2's Toffoli50 and Toffoli100 by
-- toffoliN, in src/Feynman/Verification/SOP.hs:
--
--    toffoliN = go 0
--      where go i []         = []
--            go i (x:[])     = []
--            go i (x:y:[])   = [ CNOT x y ]
--            go i (x:y:z:[]) = toffoli x y z
--            go i (x:y:xs)   =
--              let anc        = "_anc" ++ show i
--                  subproduct = toffoli x y anc
--              in subproduct ++ go (i+1) (anc:xs) ++ dagger subproduct
--
-- with toffoli its sixteen-gate Toffoli circuit (PathSum.Toffoli.
-- Depth3) and dagger = reverse . map daggerGate (src/Feynman/Core.hs).
-- Its verifyToffoliN runs it on the inputs a, b, c, … -- the controls,
-- then the target -- with the ancillas _anc0, _anc1, … listed after
-- them.  Here toffoliN is transcribed over PathSum.Adder.Feynman's
-- Primitive, the gates as the tool writes them with the wires
-- numbered, reusing PathSum.Maslov.Feynman's transcriptions of toffoli
-- (toffoliᵀ) and dagger (daggerᵀ): toffoliNᵀ.  Two departures of form,
-- neither changing the lists: goᴺ a i x xs is the tool's go i (x : xs),
-- its first wire kept apart so that it recurses structurally, and the
-- ancilla "_anc" ++ show i is read as the wire a i for a numbering a
-- of the ancillas.  The theorem is
--
--    map prim (ToffoliNᶜ n p) ≡ toffoliNᵀ (n +_) (upTo n)
--                                                     (ToffoliNᶜ-tool)
--
-- for every n ≥ 3: PathSum.ToffoliN.Tool's circuit, read gate by gate
-- as the tool writes gates, is the list the tool's toffoliN produces
-- on the inputs 0 … n − 1 with the ancillas numbered n, n + 1, …, as
-- verifyToffoliN's variable list numbers them.  The proof is by
-- induction on the layout (toffoliNᶜ-tool, on any layout whose
-- ancillas are the numbering's in order, the tool's inputs being the
-- layout's controls and then its target, inputsᴺ): at each level the
-- circuit is the tool's subproduct ++ go … ++ dagger subproduct, the
-- tool's Toffoli circuit being its toffoli (PathSum.Maslov.Feynman.
-- prim-tof₃) and PathSum.CRK.Adjoint's _† its dagger (PathSum.Maslov.
-- Feynman.prim-†); at the bottom it is the tool's toffoli.  On the
-- paper's layout the inputs are the wires 0 … n − 1 in order
-- (inputsᴺ-standard).  No closed circuit is evaluated.
--
-- As a check of the transcription: at n = 3, 4, 5 and 6 the circuit is
-- the list the tool's own functions print, copied verbatim and run
-- under GHC (ToffoliN-tool-3 … ToffoliN-tool-6: 16, 48, 80 and 112
-- gates, for which the tool's printVerStats reports 3, 5, 7 and 9
-- qubits).  These are instances of ToffoliNᶜ-tool, so they too leave
-- the circuit unevaluated.  The same run prints table 2's rows at
-- n = 50 and n = 100 (97, 190, 855, 665 and 197, 390, 1755, 1365:
-- PathSum.ToffoliN.Tool's Toffoli50ᵀ and Toffoli100ᵀ).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.ToffoliN.Feynman (M₀ : ℕ) where

open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.List.Base using
  (List; []; _∷_; _++_; map; tabulate; applyUpTo; upTo)
open import Data.List.Properties using (map-++)
open import Data.Nat.Base using (zero; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Fin.Properties as Fin

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adder.Feynman M₀ using
  (Primitive; H′; T′; Tinv′; CNOT′; prim)
open import PathSum.CRK.Adjoint M using (_†)
open import PathSum.Maslov.Feynman M₀ using (daggerᵀ; toffoliᵀ; prim-†)
open import PathSum.ToffoliN.Chain M₀ using
  (Layout; ctl; tgt; anc; inner; standard; standard-ctl; standard-tgt;
   standard-anc)
open import PathSum.ToffoliN.Tool M₀ using
  (subproduct; toffoliNᶜ; ToffoliNᶜ)

private
  variable
    N j : ℕ


------------------------------------------------------------------------
-- The tool's function, over its gates

-- SOP.hs's toffoliN, the ancilla "_anc" ++ show i being the wire a i:
-- goᴺ a i x xs is the tool's go i (x : xs).

goᴺ : (ℕ → ℕ) → ℕ → ℕ → List ℕ → List Primitive
goᴺ a i x []               = []
goᴺ a i x (y ∷ [])         = CNOT′ x y ∷ []
goᴺ a i x (y ∷ z ∷ [])     = toffoliᵀ x y z
goᴺ a i x (y ∷ v ∷ w ∷ xs) =
  toffoliᵀ x y (a i) ++ goᴺ a (suc i) (a i) (v ∷ w ∷ xs)
  ++ daggerᵀ (toffoliᵀ x y (a i))

toffoliNᵀ : (ℕ → ℕ) → List ℕ → List Primitive
toffoliNᵀ a []       = []
toffoliNᵀ a (x ∷ xs) = goᴺ a 0 x xs

-- The recursive clause, at a list ending in a given wire (so at any
-- list of four wires or more).

goᴺ-step : (a : ℕ → ℕ) (i x y v : ℕ) (ys : List ℕ) (t : ℕ) →
           goᴺ a i x (y ∷ v ∷ (ys ++ t ∷ [])) ≡
           toffoliᵀ x y (a i) ++ goᴺ a (suc i) (a i) (v ∷ (ys ++ t ∷ []))
           ++ daggerᵀ (toffoliᵀ x y (a i))
goᴺ-step a i x y v []       t = refl
goᴺ-step a i x y v (u ∷ ys) t = refl


------------------------------------------------------------------------
-- Gate for gate, on any layout

-- The tool's inputs for a layout: its controls in order, then its
-- target.

inputsᴺ : Layout N j → List ℕ
inputsᴺ L = tabulate (λ i → toℕ (ctl L i)) ++ toℕ (tgt L) ∷ []

-- With the layout's ancillas numbered a i, a (i + 1), …, the circuit is
-- the tool's go at i: its toffoli, or the subproduct and its dagger
-- around go at i + 1 on the inner layout.

toffoliNᶜ-go : (L : Layout N j) (a : ℕ → ℕ) (i : ℕ) →
               (∀ k → toℕ (anc L k) ≡ a (i + toℕ k)) →
               map prim (toffoliNᶜ L) ≡
               goᴺ a i (toℕ (ctl L zero))
                   (tabulate (λ k → toℕ (ctl L (suc k))) ++ toℕ (tgt L) ∷ [])
toffoliNᶜ-go {j = zero}  L a i h = refl
toffoliNᶜ-go {j = suc j} L a i h =
  trans (map-++ prim (subproduct L) (toffoliNᶜ (inner L) ++ subproduct L †))
  (trans (cong (map prim (subproduct L) ++_)
           (trans (map-++ prim (toffoliNᶜ (inner L)) (subproduct L †))
                  (cong₂ _++_ (toffoliNᶜ-go (inner L) a (suc i) h′)
                              (prim-† (subproduct L)))))
  (trans (cong (λ d → sub d ++ goᴺ a (suc i) d rest ++ daggerᵀ (sub d)) e)
         (sym (goᴺ-step a i (toℕ (ctl L zero)) (toℕ (ctl L (suc zero)))
                        (toℕ (ctl L (suc (suc zero)))) ys (toℕ (tgt L))))))
  where
  -- The tool's subproduct, with its ancilla d.

  sub : ℕ → List Primitive
  sub d = toffoliᵀ (toℕ (ctl L zero)) (toℕ (ctl L (suc zero))) d

  ys rest : List ℕ
  ys   = tabulate (λ k → toℕ (ctl L (suc (suc (suc k)))))
  rest = toℕ (ctl L (suc (suc zero))) ∷ (ys ++ toℕ (tgt L) ∷ [])

  -- The inner layout's ancillas are numbered from i + 1, and the
  -- subproduct's ancilla is a i.

  h′ : ∀ k → toℕ (anc (inner L) k) ≡ a (suc i + toℕ k)
  h′ k = trans (h (suc k)) (cong a (+-suc i (toℕ k)))

  e : toℕ (anc L zero) ≡ a i
  e = trans (h zero) (cong a (+-identityʳ i))

-- So the circuit is the tool's toffoliN on the layout's inputs.

toffoliNᶜ-tool : (L : Layout N j) (a : ℕ → ℕ) →
                 (∀ k → toℕ (anc L k) ≡ a (toℕ k)) →
                 map prim (toffoliNᶜ L) ≡ toffoliNᵀ a (inputsᴺ L)
toffoliNᶜ-tool L a h = toffoliNᶜ-go L a 0 h


------------------------------------------------------------------------
-- Gate for gate, on the paper's layout, for every n ≥ 3

-- Its inputs are the wires 0 … n − 1, in order, and its ancillas are
-- numbered from n on.

private
  tabulate-upTo : {k : ℕ} (f : Fin k → ℕ) (x : ℕ) (g : ℕ → ℕ) →
                  (∀ j → f j ≡ g (toℕ j)) → x ≡ g k →
                  tabulate f ++ x ∷ [] ≡ applyUpTo g (suc k)
  tabulate-upTo {zero}  f x g h e = cong (_∷ []) e
  tabulate-upTo {suc k} f x g h e =
    cong₂ _∷_ (h zero)
      (tabulate-upTo (λ j → f (suc j)) x (λ j → g (suc j))
                     (λ j → h (suc j)) e)

inputsᴺ-standard : (n : ℕ) (p : 3 ≤ n) → inputsᴺ (standard n p) ≡ upTo n
inputsᴺ-standard (suc (suc (suc j))) p@(s≤s (s≤s (s≤s z≤n))) =
  tabulate-upTo (λ i → toℕ (ctl (standard (3 + j) p) i))
                (toℕ (tgt (standard (3 + j) p))) id
                (standard-ctl (3 + j) p) (standard-tgt (3 + j) p)

standard-ancᴺ : (n : ℕ) (p : 3 ≤ n) (k : Fin (n ∸ 3)) →
                toℕ (anc (standard n p) k) ≡ n + toℕ k
standard-ancᴺ n p k =
  trans (cong toℕ (standard-anc n p k)) (Fin.toℕ-↑ʳ n k)

-- The theorem: read as the tool writes gates, the circuit is the list
-- the tool's toffoliN produces on the inputs 0 … n − 1, the ancillas
-- numbered from n on.

ToffoliNᶜ-tool : (n : ℕ) (p : 3 ≤ n) →
                 map prim (ToffoliNᶜ n p) ≡ toffoliNᵀ (n +_) (upTo n)
ToffoliNᶜ-tool n p =
  trans (toffoliNᶜ-tool (standard n p) (n +_) (standard-ancᴺ n p))
        (cong (toffoliNᵀ (n +_)) (inputsᴺ-standard n p))


------------------------------------------------------------------------
-- The tool's own lists, for n = 3, …, 6

-- As the tool's toffoli, toffoliN and dagger print them, copied
-- verbatim and run under GHC on verifyToffoliN's inputs, the wires
-- numbered by their place in its variable list
-- inputs ++ [_anc0, _anc1, …].  Each is an instance of ToffoliNᶜ-tool:
-- the circuit is not evaluated, only the transcription.

-- n = 3: 16 gates (the tool's printVerStats: 3 qubits).

ToffoliN-tool-3 :
  (p : 3 ≤ 3) →
  map prim (ToffoliNᶜ 3 p) ≡
  H′ 2 ∷ T′ 0 ∷ T′ 1 ∷ T′ 2 ∷ CNOT′ 0 1 ∷ CNOT′ 1 2 ∷ CNOT′ 2 0 ∷
  Tinv′ 0 ∷ Tinv′ 1 ∷ T′ 2 ∷ CNOT′ 1 0 ∷ Tinv′ 0 ∷ CNOT′ 1 2 ∷
  CNOT′ 2 0 ∷ CNOT′ 0 1 ∷ H′ 2 ∷ []
ToffoliN-tool-3 = ToffoliNᶜ-tool 3

-- n = 4: 48 gates (the tool's printVerStats: 5 qubits).

ToffoliN-tool-4 :
  (p : 3 ≤ 4) →
  map prim (ToffoliNᶜ 4 p) ≡
  H′ 4 ∷ T′ 0 ∷ T′ 1 ∷ T′ 4 ∷ CNOT′ 0 1 ∷ CNOT′ 1 4 ∷ CNOT′ 4 0 ∷
  Tinv′ 0 ∷ Tinv′ 1 ∷ T′ 4 ∷ CNOT′ 1 0 ∷ Tinv′ 0 ∷ CNOT′ 1 4 ∷
  CNOT′ 4 0 ∷ CNOT′ 0 1 ∷ H′ 4 ∷ H′ 3 ∷ T′ 4 ∷ T′ 2 ∷ T′ 3 ∷
  CNOT′ 4 2 ∷ CNOT′ 2 3 ∷ CNOT′ 3 4 ∷ Tinv′ 4 ∷ Tinv′ 2 ∷ T′ 3 ∷
  CNOT′ 2 4 ∷ Tinv′ 4 ∷ CNOT′ 2 3 ∷ CNOT′ 3 4 ∷ CNOT′ 4 2 ∷ H′ 3 ∷
  H′ 4 ∷ CNOT′ 0 1 ∷ CNOT′ 4 0 ∷ CNOT′ 1 4 ∷ T′ 0 ∷ CNOT′ 1 0 ∷
  Tinv′ 4 ∷ T′ 1 ∷ T′ 0 ∷ CNOT′ 4 0 ∷ CNOT′ 1 4 ∷ CNOT′ 0 1 ∷ Tinv′ 4 ∷
  Tinv′ 1 ∷ Tinv′ 0 ∷ H′ 4 ∷ []
ToffoliN-tool-4 = ToffoliNᶜ-tool 4

-- n = 5: 80 gates (the tool's printVerStats: 7 qubits).

ToffoliN-tool-5 :
  (p : 3 ≤ 5) →
  map prim (ToffoliNᶜ 5 p) ≡
  H′ 5 ∷ T′ 0 ∷ T′ 1 ∷ T′ 5 ∷ CNOT′ 0 1 ∷ CNOT′ 1 5 ∷ CNOT′ 5 0 ∷
  Tinv′ 0 ∷ Tinv′ 1 ∷ T′ 5 ∷ CNOT′ 1 0 ∷ Tinv′ 0 ∷ CNOT′ 1 5 ∷
  CNOT′ 5 0 ∷ CNOT′ 0 1 ∷ H′ 5 ∷ H′ 6 ∷ T′ 5 ∷ T′ 2 ∷ T′ 6 ∷
  CNOT′ 5 2 ∷ CNOT′ 2 6 ∷ CNOT′ 6 5 ∷ Tinv′ 5 ∷ Tinv′ 2 ∷ T′ 6 ∷
  CNOT′ 2 5 ∷ Tinv′ 5 ∷ CNOT′ 2 6 ∷ CNOT′ 6 5 ∷ CNOT′ 5 2 ∷ H′ 6 ∷
  H′ 4 ∷ T′ 6 ∷ T′ 3 ∷ T′ 4 ∷ CNOT′ 6 3 ∷ CNOT′ 3 4 ∷ CNOT′ 4 6 ∷
  Tinv′ 6 ∷ Tinv′ 3 ∷ T′ 4 ∷ CNOT′ 3 6 ∷ Tinv′ 6 ∷ CNOT′ 3 4 ∷
  CNOT′ 4 6 ∷ CNOT′ 6 3 ∷ H′ 4 ∷ H′ 6 ∷ CNOT′ 5 2 ∷ CNOT′ 6 5 ∷
  CNOT′ 2 6 ∷ T′ 5 ∷ CNOT′ 2 5 ∷ Tinv′ 6 ∷ T′ 2 ∷ T′ 5 ∷ CNOT′ 6 5 ∷
  CNOT′ 2 6 ∷ CNOT′ 5 2 ∷ Tinv′ 6 ∷ Tinv′ 2 ∷ Tinv′ 5 ∷ H′ 6 ∷ H′ 5 ∷
  CNOT′ 0 1 ∷ CNOT′ 5 0 ∷ CNOT′ 1 5 ∷ T′ 0 ∷ CNOT′ 1 0 ∷ Tinv′ 5 ∷
  T′ 1 ∷ T′ 0 ∷ CNOT′ 5 0 ∷ CNOT′ 1 5 ∷ CNOT′ 0 1 ∷ Tinv′ 5 ∷ Tinv′ 1 ∷
  Tinv′ 0 ∷ H′ 5 ∷ []
ToffoliN-tool-5 = ToffoliNᶜ-tool 5

-- n = 6: 112 gates (the tool's printVerStats: 9 qubits).

ToffoliN-tool-6 :
  (p : 3 ≤ 6) →
  map prim (ToffoliNᶜ 6 p) ≡
  H′ 6 ∷ T′ 0 ∷ T′ 1 ∷ T′ 6 ∷ CNOT′ 0 1 ∷ CNOT′ 1 6 ∷ CNOT′ 6 0 ∷
  Tinv′ 0 ∷ Tinv′ 1 ∷ T′ 6 ∷ CNOT′ 1 0 ∷ Tinv′ 0 ∷ CNOT′ 1 6 ∷
  CNOT′ 6 0 ∷ CNOT′ 0 1 ∷ H′ 6 ∷ H′ 7 ∷ T′ 6 ∷ T′ 2 ∷ T′ 7 ∷
  CNOT′ 6 2 ∷ CNOT′ 2 7 ∷ CNOT′ 7 6 ∷ Tinv′ 6 ∷ Tinv′ 2 ∷ T′ 7 ∷
  CNOT′ 2 6 ∷ Tinv′ 6 ∷ CNOT′ 2 7 ∷ CNOT′ 7 6 ∷ CNOT′ 6 2 ∷ H′ 7 ∷
  H′ 8 ∷ T′ 7 ∷ T′ 3 ∷ T′ 8 ∷ CNOT′ 7 3 ∷ CNOT′ 3 8 ∷ CNOT′ 8 7 ∷
  Tinv′ 7 ∷ Tinv′ 3 ∷ T′ 8 ∷ CNOT′ 3 7 ∷ Tinv′ 7 ∷ CNOT′ 3 8 ∷
  CNOT′ 8 7 ∷ CNOT′ 7 3 ∷ H′ 8 ∷ H′ 5 ∷ T′ 8 ∷ T′ 4 ∷ T′ 5 ∷
  CNOT′ 8 4 ∷ CNOT′ 4 5 ∷ CNOT′ 5 8 ∷ Tinv′ 8 ∷ Tinv′ 4 ∷ T′ 5 ∷
  CNOT′ 4 8 ∷ Tinv′ 8 ∷ CNOT′ 4 5 ∷ CNOT′ 5 8 ∷ CNOT′ 8 4 ∷ H′ 5 ∷
  H′ 8 ∷ CNOT′ 7 3 ∷ CNOT′ 8 7 ∷ CNOT′ 3 8 ∷ T′ 7 ∷ CNOT′ 3 7 ∷
  Tinv′ 8 ∷ T′ 3 ∷ T′ 7 ∷ CNOT′ 8 7 ∷ CNOT′ 3 8 ∷ CNOT′ 7 3 ∷ Tinv′ 8 ∷
  Tinv′ 3 ∷ Tinv′ 7 ∷ H′ 8 ∷ H′ 7 ∷ CNOT′ 6 2 ∷ CNOT′ 7 6 ∷ CNOT′ 2 7 ∷
  T′ 6 ∷ CNOT′ 2 6 ∷ Tinv′ 7 ∷ T′ 2 ∷ T′ 6 ∷ CNOT′ 7 6 ∷ CNOT′ 2 7 ∷
  CNOT′ 6 2 ∷ Tinv′ 7 ∷ Tinv′ 2 ∷ Tinv′ 6 ∷ H′ 7 ∷ H′ 6 ∷ CNOT′ 0 1 ∷
  CNOT′ 6 0 ∷ CNOT′ 1 6 ∷ T′ 0 ∷ CNOT′ 1 0 ∷ Tinv′ 6 ∷ T′ 1 ∷ T′ 0 ∷
  CNOT′ 6 0 ∷ CNOT′ 1 6 ∷ CNOT′ 0 1 ∷ Tinv′ 6 ∷ Tinv′ 1 ∷ Tinv′ 0 ∷
  H′ 6 ∷ []
ToffoliN-tool-6 = ToffoliNᶜ-tool 6
