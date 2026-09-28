------------------------------------------------------------------------
-- Presentations of groups
--
-- The Maslov decomposition exactly as the paper's tool builds it, gate
-- for gate, for every n (Amy, QPL 2018, section 5.2 and table 2)
--
-- The paper's tool, Feynman (github.com/meamy/feynman), builds the
-- circuits it verified as table 2's Maslov50 and Maslov100 by
-- maslovToffoli, in src/Feynman/Verification/SOP.hs:
--
--    maslovToffoli = go 0
--      where go i []         = []
--            go i (w:[])     = []
--            go i (w:z:[])   = [CNOT w z]
--            go i (w:x:z:[]) = toffoli w x z
--            go i (w:x:y:xs) =
--              let anc = "_anc" ++ show i
--                  sub = rToffoli4 w x y anc
--              in sub ++ go (i+1) (anc:xs) ++ (dagger sub)
--
-- Here toffoli is the tool's sixteen-gate Toffoli circuit
-- (PathSum.Toffoli.Depth3), rToffoli4 w x y z is
--
--    conj ++ [CNOT w z, T z, CNOT x z, Tinv z,
--             CNOT w z, T z, CNOT x z, Tinv z] ++ conj,
--    conj = [H z, T z, CNOT y z, Tinv z, H z],
--
-- and dagger = reverse . map daggerGate (src/Feynman/Core.hs) runs the
-- gates last to first, T and T† exchanged.  The tool's verifyMaslovN
-- runs it on the inputs a, b, c, … -- the controls, then the target --
-- with the ancillas _anc0, _anc1, … listed after them.  The four
-- functions are transcribed here over PathSum.Adder.Feynman's
-- Primitive, the gates as the tool writes them with the wires numbered:
-- toffoliᵀ, rToffoli4ᵀ, daggerGateᵀ and daggerᵀ, and maslovToffoliᵀ.
-- Two departures of form, neither changing the lists: goᵀ a i w ws is
-- the tool's go i (w : ws), its first wire kept apart so that it
-- recurses structurally, and the ancilla "_anc" ++ show i is read as
-- the wire a i for a numbering a of the ancillas.  The theorem is
--
--    map prim (Maslovₙ n p) ≡ maslovToffoliᵀ (n +_) (upTo n)
--                                                     (Maslovₙ-tool)
--
-- for every n ≥ 3: PathSum.Maslov's circuit, read gate by gate as the
-- tool writes gates, is the list the tool's maslovToffoli produces on
-- the inputs 0 … n − 1 with the ancillas numbered n, n + 1, …, as
-- verifyMaslovN's variable list numbers them.  The proof is by
-- induction on the layout (maslov-tool, on any layout whose ancillas
-- are the numbering's in order, the tool's inputs being the layout's
-- controls and then its target, inputsᵀ): at each level the circuit is
-- the tool's sub ++ go … ++ dagger sub, the Toffoli-4 gate rc3x being
-- the tool's rToffoli4 (prim-rc3x) and PathSum.CRK.Adjoint's _† the
-- tool's dagger (prim-†); at the bottom it is the tool's CNOT or its
-- toffoli (prim-tof₃).  On the paper's layout the inputs are wires
-- 0 … n − 1 in order (inputsᵀ-standard).  No closed circuit is
-- evaluated.
--
-- As a check of the transcription: at n = 3, …, 7 the circuit is the
-- list the tool's own functions print, copied verbatim and run under
-- GHC (Maslov-tool-3 … Maslov-tool-7: 16, 37, 52, 73 and 88 gates,
-- for which the tool's printVerStats reports 3, 5, 6, 8 and 9 qubits).
-- These are instances of Maslovₙ-tool, so they too leave the circuit
-- unevaluated.  The same run prints table 2's rows at n = 50 and
-- n = 100 (74, 192, 481, 384 and 149, 392, 981, 784: PathSum.Maslov's
-- table-2-Maslov50 and table-2-Maslov100), and at the odd n = 51 and
-- n = 101, which the table does not list, 75, 194, 489, 391 and 150,
-- 394, 989, 791: PathSum.Maslov's counts, now that its middle gate is
-- the tool's Toffoli circuit (stats-Maslov51, stats-Maslov101; with
-- PathSum.Toffoli's tof there the Clifford counts were one lower).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Maslov.Feynman (M₀ : ℕ) where

open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.List.Base using
  (List; []; _∷_; _++_; map; reverse; tabulate; applyUpTo; upTo)
open import Data.List.Properties using (map-++; reverse-map)
open import Data.Nat.Base using (zero; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product.Base using (_×_; _,_)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adder.Feynman M₀ using
  (Primitive; H′; T′; Tinv′; CNOT′; R′; R†′; prim)
open import PathSum.CRK.Adjoint M using (inv; _†; †-reverse)
open import PathSum.CRK.Path M₀ using
  (Gate; H; CNOT; R; R†; Circuit; paths)
open import PathSum.CRK.Qubits M₀ using (qubits)
open import PathSum.Maslov M₀ using
  (maslov; Maslovₙ; Maslovₙ-qubits; Maslovₙ-paths; Maslovₙ-cliffords;
   Maslovₙ-tcount)
open import PathSum.Maslov.Chain M₀ using
  (Layout; ctl; tgt; anc; c₀; c₁; c₂; a₀; c₀≢a₀; c₁≢a₀; c₂≢a₀; inner;
   standardᴹ; standardᴹ-ctl; standardᴹ-tgt; standardᴹ-anc)
open import PathSum.Maslov.Gate4 M₀ using (rc3x)
open import PathSum.QFT.Count M₀ using (cliffords)
open import PathSum.Toffoli.Depth3 M₀ using (tof₃)
open import PathSum.Toffoli.Netlist M₀ using (tcount)

private
  variable
    n N m : ℕ


------------------------------------------------------------------------
-- The tool's functions, over its gates

-- Feynman.Core's daggerGate and dagger: H and CNOT are their own
-- inverses, T and T† each other's (and, beyond the tool's gates, so are
-- R_k and R_k† for the other k, which prim writes as R′ and R†′).

daggerGateᵀ : Primitive → Primitive
daggerGateᵀ (H′ x)      = H′ x
daggerGateᵀ (T′ x)      = Tinv′ x
daggerGateᵀ (Tinv′ x)   = T′ x
daggerGateᵀ (CNOT′ x y) = CNOT′ x y
daggerGateᵀ (R′ k x)    = R†′ k x
daggerGateᵀ (R†′ k x)   = R′ k x

daggerᵀ : List Primitive → List Primitive
daggerᵀ gs = reverse (map daggerGateᵀ gs)

-- SOP.hs's toffoli.

toffoliᵀ : ℕ → ℕ → ℕ → List Primitive
toffoliᵀ x y z =
  H′ z ∷ T′ x ∷ T′ y ∷ T′ z ∷ CNOT′ x y ∷ CNOT′ y z ∷ CNOT′ z x ∷
  Tinv′ x ∷ Tinv′ y ∷ T′ z ∷ CNOT′ y x ∷ Tinv′ x ∷
  CNOT′ y z ∷ CNOT′ z x ∷ CNOT′ x y ∷ H′ z ∷ []

-- SOP.hs's rToffoli4.

rToffoli4ᵀ : ℕ → ℕ → ℕ → ℕ → List Primitive
rToffoli4ᵀ w x y z =
  conj ++ (CNOT′ w z ∷ T′ z ∷ CNOT′ x z ∷ Tinv′ z ∷
           CNOT′ w z ∷ T′ z ∷ CNOT′ x z ∷ Tinv′ z ∷ []) ++ conj
  where
  conj : List Primitive
  conj = H′ z ∷ T′ z ∷ CNOT′ y z ∷ Tinv′ z ∷ H′ z ∷ []

-- SOP.hs's maslovToffoli, the ancilla "_anc" ++ show i being the wire
-- a i: goᵀ a i w ws is the tool's go i (w : ws).

goᵀ : (ℕ → ℕ) → ℕ → ℕ → List ℕ → List Primitive
goᵀ a i w []               = []
goᵀ a i w (z ∷ [])         = CNOT′ w z ∷ []
goᵀ a i w (x ∷ z ∷ [])     = toffoliᵀ w x z
goᵀ a i w (x ∷ y ∷ v ∷ xs) =
  rToffoli4ᵀ w x y (a i) ++ goᵀ a (suc i) (a i) (v ∷ xs)
  ++ daggerᵀ (rToffoli4ᵀ w x y (a i))

maslovToffoliᵀ : (ℕ → ℕ) → List ℕ → List Primitive
maslovToffoliᵀ a []       = []
maslovToffoliᵀ a (w ∷ ws) = goᵀ a 0 w ws

-- The recursive clause, at a list ending in a given wire (so at any
-- list of four wires or more).

goᵀ-step : (a : ℕ → ℕ) (i w x y : ℕ) (ys : List ℕ) (t : ℕ) →
           goᵀ a i w (x ∷ y ∷ (ys ++ t ∷ [])) ≡
           rToffoli4ᵀ w x y (a i) ++ goᵀ a (suc i) (a i) (ys ++ t ∷ [])
           ++ daggerᵀ (rToffoli4ᵀ w x y (a i))
goᵀ-step a i w x y []       t = refl
goᵀ-step a i w x y (v ∷ ys) t = refl


------------------------------------------------------------------------
-- The gates, as the tool writes them

-- The inverse of a gate is the tool's daggerGate, so the adjoint of
-- PathSum.CRK.Adjoint is the tool's dagger.

prim-inv : (g : Gate n) → prim (inv g) ≡ daggerGateᵀ (prim g)
prim-inv (H _)                            = refl
prim-inv (CNOT _ _ _)                     = refl
prim-inv (R zero _)                       = refl
prim-inv (R (suc zero) _)                 = refl
prim-inv (R (suc (suc zero)) _)           = refl
prim-inv (R (suc (suc (suc zero))) _)     = refl
prim-inv (R (suc (suc (suc (suc _)))) _)  = refl
prim-inv (R† zero _)                      = refl
prim-inv (R† (suc zero) _)                = refl
prim-inv (R† (suc (suc zero)) _)          = refl
prim-inv (R† (suc (suc (suc zero))) _)    = refl
prim-inv (R† (suc (suc (suc (suc _)))) _) = refl

private
  map-prim-inv : (C : Circuit n) →
                 map prim (map inv C) ≡ map daggerGateᵀ (map prim C)
  map-prim-inv []      = refl
  map-prim-inv (g ∷ C) = cong₂ _∷_ (prim-inv g) (map-prim-inv C)

prim-† : (C : Circuit n) → map prim (C †) ≡ daggerᵀ (map prim C)
prim-† C =
  trans (cong (map prim) (†-reverse C))
  (trans (map-prim-inv (reverse C))
  (trans (cong (map daggerGateᵀ) (reverse-map prim C))
         (reverse-map daggerGateᵀ (map prim C))))

-- The relative-phase Toffoli-4 gate is the tool's rToffoli4, and the
-- tool's Toffoli circuit its toffoli.

prim-rc3x : (a b c d : Fin n) (p : a ≢ d) (q : b ≢ d) (r : c ≢ d) →
            map prim (rc3x a b c d p q r) ≡
            rToffoli4ᵀ (toℕ a) (toℕ b) (toℕ c) (toℕ d)
prim-rc3x a b c d p q r = refl

prim-tof₃ : (c₁ c₂ t : Fin n) (p : c₁ ≢ c₂) (q : c₁ ≢ t) (r : c₂ ≢ t) →
            map prim (tof₃ c₁ c₂ t p q r) ≡
            toffoliᵀ (toℕ c₁) (toℕ c₂) (toℕ t)
prim-tof₃ c₁ c₂ t p q r = refl


------------------------------------------------------------------------
-- Gate for gate, on any layout

-- The tool's inputs for a layout: its controls in order, then its
-- target.

inputsᵀ : Layout N m → List ℕ
inputsᵀ L = tabulate (λ i → toℕ (ctl L i)) ++ toℕ (tgt L) ∷ []

-- With the layout's ancillas numbered a i, a (i + 1), …, the circuit is
-- the tool's go at i: a CNOT, the tool's toffoli, or rToffoli4 and its
-- dagger around go at i + 1 on the inner layout.

maslov-go : (L : Layout N m) (a : ℕ → ℕ) (i : ℕ) →
            (∀ j → toℕ (anc L j) ≡ a (i + toℕ j)) →
            map prim (maslov L) ≡
            goᵀ a i (toℕ (ctl L zero))
                (tabulate (λ j → toℕ (ctl L (suc j))) ++ toℕ (tgt L) ∷ [])
maslov-go {m = zero}        L a i h = refl
maslov-go {m = suc zero}    L a i h = refl
maslov-go {m = suc (suc m)} L a i h =
  trans (map-++ prim G (maslov (inner L) ++ G †))
  (trans (cong (map prim G ++_)
               (trans (map-++ prim (maslov (inner L)) (G †))
                      (cong₂ _++_ (maslov-go (inner L) a (suc i) h′)
                                  (prim-† G))))
  (trans (cong (λ d → sub d ++ goᵀ a (suc i) d rest ++ daggerᵀ (sub d)) e)
         (sym (goᵀ-step a i (toℕ (c₀ L)) (toℕ (c₁ L)) (toℕ (c₂ L)) ys
                        (toℕ (tgt L))))))
  where
  G : Circuit _
  G = rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L) (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L)

  -- The tool's sub, with its ancilla d.

  sub : ℕ → List Primitive
  sub d = rToffoli4ᵀ (toℕ (c₀ L)) (toℕ (c₁ L)) (toℕ (c₂ L)) d

  ys rest : List ℕ
  ys   = tabulate (λ j → toℕ (ctl L (suc (suc (suc j)))))
  rest = ys ++ toℕ (tgt L) ∷ []

  -- The inner layout's ancillas are numbered from i + 1, and the first
  -- gate's ancilla is a i.

  h′ : ∀ j → toℕ (anc (inner L) j) ≡ a (suc i + toℕ j)
  h′ j = trans (h (suc j)) (cong a (+-suc i (toℕ j)))

  e : toℕ (a₀ L) ≡ a i
  e = trans (h zero) (cong a (+-identityʳ i))

-- So the circuit is the tool's maslovToffoli on the layout's inputs.

maslov-tool : (L : Layout N m) (a : ℕ → ℕ) →
              (∀ j → toℕ (anc L j) ≡ a (toℕ j)) →
              map prim (maslov L) ≡ maslovToffoliᵀ a (inputsᵀ L)
maslov-tool L a h = maslov-go L a 0 h


------------------------------------------------------------------------
-- Gate for gate, on the paper's layout, for every n ≥ 3

-- Its inputs are the wires 0 … n − 1, in order.

private
  tabulate-upTo : {k : ℕ} (f : Fin k → ℕ) (x : ℕ) (g : ℕ → ℕ) →
                  (∀ j → f j ≡ g (toℕ j)) → x ≡ g k →
                  tabulate f ++ x ∷ [] ≡ applyUpTo g (suc k)
  tabulate-upTo {zero}  f x g h e = cong (_∷ []) e
  tabulate-upTo {suc k} f x g h e =
    cong₂ _∷_ (h zero)
      (tabulate-upTo (λ j → f (suc j)) x (λ j → g (suc j))
                     (λ j → h (suc j)) e)

inputsᵀ-standard : (n : ℕ) (p : 3 ≤ n) → inputsᵀ (standardᴹ n p) ≡ upTo n
inputsᵀ-standard (suc (suc (suc m))) p@(s≤s (s≤s (s≤s z≤n))) =
  tabulate-upTo (λ i → toℕ (ctl (standardᴹ (3 + m) p) i))
                (toℕ (tgt (standardᴹ (3 + m) p))) id
                (standardᴹ-ctl (3 + m) p) (standardᴹ-tgt (3 + m) p)

-- The theorem: read as the tool writes gates, the circuit is the list
-- the tool's maslovToffoli produces on the inputs 0 … n − 1, the
-- ancillas numbered from n on.

Maslovₙ-tool : (n : ℕ) (p : 3 ≤ n) →
               map prim (Maslovₙ n p) ≡ maslovToffoliᵀ (n +_) (upTo n)
Maslovₙ-tool n p =
  trans (maslov-tool (standardᴹ n p) (n +_) (standardᴹ-anc n p))
        (cong (maslovToffoliᵀ (n +_)) (inputsᵀ-standard n p))


------------------------------------------------------------------------
-- The tool's own lists, for n = 3, …, 7

-- As the tool's toffoli, rToffoli4, maslovToffoli and dagger print
-- them, copied verbatim and run under GHC on verifyMaslovN's inputs,
-- the wires numbered by their place in its variable list
-- inputs ++ [_anc0, _anc1, …].  Each is an instance of Maslovₙ-tool:
-- the circuit is not evaluated, only the transcription.

-- n = 3: 16 gates (the tool's printVerStats: 3 qubits).

Maslov-tool-3 :
  (p : 3 ≤ 3) →
  map prim (Maslovₙ 3 p) ≡
  H′ 2 ∷ T′ 0 ∷ T′ 1 ∷ T′ 2 ∷ CNOT′ 0 1 ∷ CNOT′ 1 2 ∷ CNOT′ 2 0 ∷
  Tinv′ 0 ∷ Tinv′ 1 ∷ T′ 2 ∷ CNOT′ 1 0 ∷ Tinv′ 0 ∷ CNOT′ 1 2 ∷
  CNOT′ 2 0 ∷ CNOT′ 0 1 ∷ H′ 2 ∷ []
Maslov-tool-3 = Maslovₙ-tool 3

-- n = 4: 37 gates (the tool's printVerStats: 5 qubits).

Maslov-tool-4 :
  (p : 3 ≤ 4) →
  map prim (Maslovₙ 4 p) ≡
  H′ 4 ∷ T′ 4 ∷ CNOT′ 2 4 ∷ Tinv′ 4 ∷ H′ 4 ∷ CNOT′ 0 4 ∷ T′ 4 ∷
  CNOT′ 1 4 ∷ Tinv′ 4 ∷ CNOT′ 0 4 ∷ T′ 4 ∷ CNOT′ 1 4 ∷ Tinv′ 4 ∷ H′ 4 ∷
  T′ 4 ∷ CNOT′ 2 4 ∷ Tinv′ 4 ∷ H′ 4 ∷ CNOT′ 4 3 ∷ H′ 4 ∷ T′ 4 ∷
  CNOT′ 2 4 ∷ Tinv′ 4 ∷ H′ 4 ∷ T′ 4 ∷ CNOT′ 1 4 ∷ Tinv′ 4 ∷ CNOT′ 0 4 ∷
  T′ 4 ∷ CNOT′ 1 4 ∷ Tinv′ 4 ∷ CNOT′ 0 4 ∷ H′ 4 ∷ T′ 4 ∷ CNOT′ 2 4 ∷
  Tinv′ 4 ∷ H′ 4 ∷ []
Maslov-tool-4 = Maslovₙ-tool 4

-- n = 5: 52 gates (the tool's printVerStats: 6 qubits).

Maslov-tool-5 :
  (p : 3 ≤ 5) →
  map prim (Maslovₙ 5 p) ≡
  H′ 5 ∷ T′ 5 ∷ CNOT′ 2 5 ∷ Tinv′ 5 ∷ H′ 5 ∷ CNOT′ 0 5 ∷ T′ 5 ∷
  CNOT′ 1 5 ∷ Tinv′ 5 ∷ CNOT′ 0 5 ∷ T′ 5 ∷ CNOT′ 1 5 ∷ Tinv′ 5 ∷ H′ 5 ∷
  T′ 5 ∷ CNOT′ 2 5 ∷ Tinv′ 5 ∷ H′ 5 ∷ H′ 4 ∷ T′ 5 ∷ T′ 3 ∷ T′ 4 ∷
  CNOT′ 5 3 ∷ CNOT′ 3 4 ∷ CNOT′ 4 5 ∷ Tinv′ 5 ∷ Tinv′ 3 ∷ T′ 4 ∷
  CNOT′ 3 5 ∷ Tinv′ 5 ∷ CNOT′ 3 4 ∷ CNOT′ 4 5 ∷ CNOT′ 5 3 ∷ H′ 4 ∷
  H′ 5 ∷ T′ 5 ∷ CNOT′ 2 5 ∷ Tinv′ 5 ∷ H′ 5 ∷ T′ 5 ∷ CNOT′ 1 5 ∷
  Tinv′ 5 ∷ CNOT′ 0 5 ∷ T′ 5 ∷ CNOT′ 1 5 ∷ Tinv′ 5 ∷ CNOT′ 0 5 ∷ H′ 5 ∷
  T′ 5 ∷ CNOT′ 2 5 ∷ Tinv′ 5 ∷ H′ 5 ∷ []
Maslov-tool-5 = Maslovₙ-tool 5

-- n = 6: 73 gates (the tool's printVerStats: 8 qubits).

Maslov-tool-6 :
  (p : 3 ≤ 6) →
  map prim (Maslovₙ 6 p) ≡
  H′ 6 ∷ T′ 6 ∷ CNOT′ 2 6 ∷ Tinv′ 6 ∷ H′ 6 ∷ CNOT′ 0 6 ∷ T′ 6 ∷
  CNOT′ 1 6 ∷ Tinv′ 6 ∷ CNOT′ 0 6 ∷ T′ 6 ∷ CNOT′ 1 6 ∷ Tinv′ 6 ∷ H′ 6 ∷
  T′ 6 ∷ CNOT′ 2 6 ∷ Tinv′ 6 ∷ H′ 6 ∷ H′ 7 ∷ T′ 7 ∷ CNOT′ 4 7 ∷
  Tinv′ 7 ∷ H′ 7 ∷ CNOT′ 6 7 ∷ T′ 7 ∷ CNOT′ 3 7 ∷ Tinv′ 7 ∷ CNOT′ 6 7 ∷
  T′ 7 ∷ CNOT′ 3 7 ∷ Tinv′ 7 ∷ H′ 7 ∷ T′ 7 ∷ CNOT′ 4 7 ∷ Tinv′ 7 ∷
  H′ 7 ∷ CNOT′ 7 5 ∷ H′ 7 ∷ T′ 7 ∷ CNOT′ 4 7 ∷ Tinv′ 7 ∷ H′ 7 ∷ T′ 7 ∷
  CNOT′ 3 7 ∷ Tinv′ 7 ∷ CNOT′ 6 7 ∷ T′ 7 ∷ CNOT′ 3 7 ∷ Tinv′ 7 ∷
  CNOT′ 6 7 ∷ H′ 7 ∷ T′ 7 ∷ CNOT′ 4 7 ∷ Tinv′ 7 ∷ H′ 7 ∷ H′ 6 ∷ T′ 6 ∷
  CNOT′ 2 6 ∷ Tinv′ 6 ∷ H′ 6 ∷ T′ 6 ∷ CNOT′ 1 6 ∷ Tinv′ 6 ∷ CNOT′ 0 6 ∷
  T′ 6 ∷ CNOT′ 1 6 ∷ Tinv′ 6 ∷ CNOT′ 0 6 ∷ H′ 6 ∷ T′ 6 ∷ CNOT′ 2 6 ∷
  Tinv′ 6 ∷ H′ 6 ∷ []
Maslov-tool-6 = Maslovₙ-tool 6

-- n = 7: 88 gates (the tool's printVerStats: 9 qubits).

Maslov-tool-7 :
  (p : 3 ≤ 7) →
  map prim (Maslovₙ 7 p) ≡
  H′ 7 ∷ T′ 7 ∷ CNOT′ 2 7 ∷ Tinv′ 7 ∷ H′ 7 ∷ CNOT′ 0 7 ∷ T′ 7 ∷
  CNOT′ 1 7 ∷ Tinv′ 7 ∷ CNOT′ 0 7 ∷ T′ 7 ∷ CNOT′ 1 7 ∷ Tinv′ 7 ∷ H′ 7 ∷
  T′ 7 ∷ CNOT′ 2 7 ∷ Tinv′ 7 ∷ H′ 7 ∷ H′ 8 ∷ T′ 8 ∷ CNOT′ 4 8 ∷
  Tinv′ 8 ∷ H′ 8 ∷ CNOT′ 7 8 ∷ T′ 8 ∷ CNOT′ 3 8 ∷ Tinv′ 8 ∷ CNOT′ 7 8 ∷
  T′ 8 ∷ CNOT′ 3 8 ∷ Tinv′ 8 ∷ H′ 8 ∷ T′ 8 ∷ CNOT′ 4 8 ∷ Tinv′ 8 ∷
  H′ 8 ∷ H′ 6 ∷ T′ 8 ∷ T′ 5 ∷ T′ 6 ∷ CNOT′ 8 5 ∷ CNOT′ 5 6 ∷
  CNOT′ 6 8 ∷ Tinv′ 8 ∷ Tinv′ 5 ∷ T′ 6 ∷ CNOT′ 5 8 ∷ Tinv′ 8 ∷
  CNOT′ 5 6 ∷ CNOT′ 6 8 ∷ CNOT′ 8 5 ∷ H′ 6 ∷ H′ 8 ∷ T′ 8 ∷ CNOT′ 4 8 ∷
  Tinv′ 8 ∷ H′ 8 ∷ T′ 8 ∷ CNOT′ 3 8 ∷ Tinv′ 8 ∷ CNOT′ 7 8 ∷ T′ 8 ∷
  CNOT′ 3 8 ∷ Tinv′ 8 ∷ CNOT′ 7 8 ∷ H′ 8 ∷ T′ 8 ∷ CNOT′ 4 8 ∷ Tinv′ 8 ∷
  H′ 8 ∷ H′ 7 ∷ T′ 7 ∷ CNOT′ 2 7 ∷ Tinv′ 7 ∷ H′ 7 ∷ T′ 7 ∷ CNOT′ 1 7 ∷
  Tinv′ 7 ∷ CNOT′ 0 7 ∷ T′ 7 ∷ CNOT′ 1 7 ∷ Tinv′ 7 ∷ CNOT′ 0 7 ∷ H′ 7 ∷
  T′ 7 ∷ CNOT′ 2 7 ∷ Tinv′ 7 ∷ H′ 7 ∷ []
Maslov-tool-7 = Maslovₙ-tool 7


------------------------------------------------------------------------
-- The tool's counts at odd n

-- The same GHC run of the tool's printVerStats at n = 51 and n = 101,
-- which table 2 does not list: 75 and 150 qubits, 194 and 394 path
-- variables, 489 and 989 Clifford gates, 391 and 791 T gates -- the
-- counts of PathSum.Maslov, computed from the circuit.  (With
-- PathSum.Toffoli's eight-Clifford tof in the middle the Clifford
-- counts would be 488 and 988.)

stats-Maslov51 : (p : 3 ≤ 51) →
                 (qubits (Maslovₙ 51 p) ≡ 75) × (paths (Maslovₙ 51 p) ≡ 194)
                 × (cliffords (Maslovₙ 51 p) ≡ 489)
                 × (tcount (Maslovₙ 51 p) ≡ 391)
stats-Maslov51 p =
  Maslovₙ-qubits 51 p , Maslovₙ-paths 51 p , Maslovₙ-cliffords 51 p
  , Maslovₙ-tcount 51 p

stats-Maslov101 : (p : 3 ≤ 101) →
                  (qubits (Maslovₙ 101 p) ≡ 150)
                  × (paths (Maslovₙ 101 p) ≡ 394)
                  × (cliffords (Maslovₙ 101 p) ≡ 989)
                  × (tcount (Maslovₙ 101 p) ≡ 791)
stats-Maslov101 p =
  Maslovₙ-qubits 101 p , Maslovₙ-paths 101 p , Maslovₙ-cliffords 101 p
  , Maslovₙ-tcount 101 p
