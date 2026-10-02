------------------------------------------------------------------------
-- Presentations of groups
--
-- The hidden shift benchmark as the paper's tool generates it, over
-- {H, X, CNOT, R_k, R_k†}, correct for every random draw (Amy, QPL
-- 2018, section 5.2 and table 2)
--
-- The paper's tool, Feynman (src/Feynman/Verification/SOP.hs as of
-- the paper), draws its hidden shift instances at random with
-- QuickCheck.  For n = 2m qubits and A "alternations" it draws a shift
-- s, a sublist of the n wires, and a Maiorana-McFarland function g on
-- the first m wires (genMaioranaG): A alternations, each a ccz on three
-- distinct wires followed by 200 draws, each either a cz on two
-- distinct wires or a Z on one.  The circuit is
--
--    H^n ++ (X^s ++ g ++ cTrans ++ X^s) ++ H^n ++ (g′ ++ cTrans) ++ H^n
--
-- where cTrans is a cz between wires i and i + m for every i < m and
-- g′ is g moved to the second half of the wires.  Here the draws are
-- data: Draw m (a cz with its two distinct wires, or a Z) and Block d m
-- (the ccz's three distinct wires and d draws; the tool's d is 200),
-- so every draw the tool can make is a value of these types.  The
-- gates: the tool's ccz is PathSum.HiddenShift.ToolCCZ's cczᶜ, its cz
-- PathSum.HiddenShift.Gates's CZᶜ (S, S, CNOT, S†, CNOT, literally),
-- its Z the gate R₁, X a primitive gate (PathSum.CRK.WithX), so the
-- circuit (HSᵗ s Bs) has 3n Hadamards and 3n path variables, as in
-- table 2.  PathSum.HiddenShift.Feynman shows that it is the tool's
-- list gate for gate; this module shows it correct.
--
-- The monomials drawn (gTerms) are those of the ccz, cz and Z gates,
-- and the oracle circuits are the diagonals (-1)^f and (-1)^{f̃} of
-- the Maiorana-McFarland function f(x, y) = g(x) + x·y and its dual,
-- g the sum of the drawn monomials (Signs-Oᶠᵗ, Signs-Oᵈᵗ: the ccz by
-- ToolCCZ, the cz and Z by Gates).  So, as in
-- PathSum.HiddenShift.Circuit, each layer simulates a layer of
-- PathSum.HiddenShift's composite HS, now with X^s exact
-- (PathSum.HiddenShift.LayersX), and for every m, every s and every
-- draw (hidden-shift-tool-≋)
--
--    ⟦ HSᵗ s Bs ⟧ ≋ HS (sumᴾ (gTerms Bs)) s ,
--
-- so from |0⟩ the circuit reaches |s⟩ with normalised amplitude 1 and
-- nothing else (hidden-shift-tool), its path-sum with every input read
-- as 0 is |x⟩ ↦ |s⟩ (hidden-shift-tool-set0: the tool's
-- verifyHiddenShift, which checks the circuit against
-- hiddenShiftSpec with every input 0), and every complete reduction by
-- the rules of figure 2 ends there (tool-reduces); one exists, of
-- exactly 3n steps (PathSum.HiddenShift.ToolExists).  It is, up to ≋,
-- PathSum.HiddenShift.Circuit's circuit of figure 3(a) on the same
-- monomials, which writes X as H R₁ H and CCZ as Gates's CCZᶜ
-- (tool-≋-figure3a).  The symbolic shift is
-- PathSum.HiddenShift.ToolSymbolic.
--
-- What is not formalised: the random draws themselves.  The theorems
-- hold for every draw, so for whatever the tool drew; QuickCheck's
-- distribution plays no part.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Tool (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-comm; xor-assoc)
open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (0ℤ; +_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.Nat.Base using (suc) renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_)
open import Data.Vec.Base using (Vec; toList)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

import Data.Fin.Properties as Fin

open import PathSum.Ancilla.Register M₀ using
  (set0ᶜ; amp-input; _≋⟨_⟩₀_; ≋⟨⟩₀-set0ᶜ)
open import PathSum.Assign using ([_]ᶻ; same)
open import PathSum.Base using (PathSum; out; phase)
open import PathSum.Cyclotomic M₀ using (0ᴬ; _≐_; zpow; scale; scale-map)
open import PathSum.AmpLinear M₀ using (scale-exp)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_; ≋-sym; ≋-trans)
open import PathSum.HiddenShift M₀ using
  (Hᴾ; mmᴾ; dualᴾ; HS; hs-norm; specᴾ; amp-specᴾ; hidden-shift;
   scale-0ᴬ)
open import PathSum.HiddenShift.Circuit M₀ using
  (sumᴾ; xyTerms; onLeft; onRight; fTerms; f̃Terms; bool-f; bool-f̃;
   allMask; HSᶜ; hidden-shift-circuit-≋)
open import PathSum.HiddenShift.Gates M₀ using
  (Term; Z; CZ; CCZ; sumᵇ; sumᵇ-++; mapTerm; oracle; norm-oracle;
   Signs; Signs-[]; Signs-++; Signs-cong; Signs-oracle)
open import PathSum.HiddenShift.Layers M₀ using
  (hadamards; norm-hadamards; Sim; Sim-signs; Sim-hadamards)
open import PathSum.HiddenShift.LayersX M₀ using
  (norm-++ˣ; Sim-embed; Sim-++ˣ; Sim-circuitˣ; Sim-≋ˣ; flipsˣ;
   norm-flipsˣ; Sim-shiftedˣ)
open import PathSum.HiddenShift.Sign M₀ using (1ᴬ)
open import PathSum.HiddenShift.Simulation M₀ using
  (at0; amp-at0; spec-only-if)
open import PathSum.HiddenShift.ToolCCZ M₀ using (cczᶜ; Signs-ccz)
open import PathSum.HiddenShift.Walsh using (0ᵃ)
open import PathSum.Polynomial using (0ᴾ; κ; _≈[_]_)

open +-*-Solver using (solve; con; _:+_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

import PathSum.CRK.Circuit
import PathSum.CRK.Semantics

private
  module CRK  = PathSum.CRK.Circuit M
  module CRKˢ = PathSum.CRK.Semantics M₀

open import PathSum.CRK.Adjoint M using (norm-++)
open import PathSum.CRK.WithX M₀ using
  (Circuit; norm; ⟦_⟧; embed; norm-embed; applyᴬ)
open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Order M using (pow)

private
  variable
    n m d : ℕ


------------------------------------------------------------------------
-- The draws

-- One of the draws after a ccz: a cz on two distinct wires (the tool's
-- genCZ), or a Z on one (genZ).

data Draw (m : ℕ) : Set where
  CZᵈ : (a b : Fin m) → a ≢ b → Draw m
  Zᵈ  : Fin m → Draw m

-- One alternation: the ccz's three distinct wires (the tool's genCCZ
-- draws x, then y among the others, then z among the rest) and d
-- draws (the tool's d is 200).

record Block (d m : ℕ) : Set where
  constructor block
  field
    ccz₁ ccz₂ ccz₃ : Fin m
    ccz₁≢ccz₂      : ccz₁ ≢ ccz₂
    ccz₁≢ccz₃      : ccz₁ ≢ ccz₃
    ccz₂≢ccz₃      : ccz₂ ≢ ccz₃
    draws          : Vec (Draw m) d

-- The monomial each gate contributes to g.

drawTerm : Draw m → Term m
drawTerm (CZᵈ a b p) = CZ a b p
drawTerm (Zᵈ a)      = Z a

gTerms : List (Block d m) → List (Term m)
gTerms []                          = []
gTerms (block a b c p q r ds ∷ Bs) =
  CCZ a b c p q r ∷ (map drawTerm (toList ds) ++ gTerms Bs)


------------------------------------------------------------------------
-- The oracle circuits

-- The gates of the draws on the wires ρ i, ρ an injection: the tool's
-- ccz, then its cz or Z for each draw (Gates's termᶜ of the monomial).

blockᶜ : (ρ : Fin m → Fin n) → (∀ {a b} → ρ a ≡ ρ b → a ≡ b) →
         Block d m → CRK.Circuit n
blockᶜ ρ inj (block a b c p q r ds) =
  cczᶜ (ρ a) (ρ b) (ρ c) (λ e → p (inj e)) (λ e → q (inj e))
       (λ e → r (inj e)) ++
  oracle (map (mapTerm ρ inj) (map drawTerm (toList ds)))

gᶜ : (ρ : Fin m → Fin n) → (∀ {a b} → ρ a ≡ ρ b → a ≡ b) →
     List (Block d m) → CRK.Circuit n
gᶜ ρ inj []       = []
gᶜ ρ inj (B ∷ Bs) = blockᶜ ρ inj B ++ gᶜ ρ inj Bs

norm-gᶜ : (ρ : Fin m → Fin n) (inj : ∀ {a b} → ρ a ≡ ρ b → a ≡ b)
          (Bs : List (Block d m)) → CRK.norm (gᶜ ρ inj Bs) ≡ 0
norm-gᶜ ρ inj []                            = refl
norm-gᶜ ρ inj (B@(block a b c p q r ds) ∷ Bs) =
  trans (norm-++ (blockᶜ ρ inj B) (gᶜ ρ inj Bs))
    (cong₂ _ℕ+_
      (trans (norm-++ (cczᶜ (ρ a) (ρ b) (ρ c) (λ e → p (inj e))
                            (λ e → q (inj e)) (λ e → r (inj e)))
                      (oracle (map (mapTerm ρ inj) (map drawTerm (toList ds)))))
             (norm-oracle (map (mapTerm ρ inj) (map drawTerm (toList ds)))))
      (norm-gᶜ ρ inj Bs))

-- It multiplies the entry at z by (-1) to the sum of the monomials,
-- read on the wires ρ.

Signs-gᶜ : (ρ : Fin m → Fin n) (inj : ∀ {a b} → ρ a ≡ ρ b → a ≡ b)
           (Bs : List (Block d m)) →
           Signs (gᶜ ρ inj Bs) (sumᵇ (map (mapTerm ρ inj) (gTerms Bs)))
Signs-gᶜ ρ inj []                          = Signs-[]
Signs-gᶜ ρ inj (block a b c p q r ds ∷ Bs) =
  Signs-cong (Signs-++ (Signs-++ (Signs-ccz (ρ a) (ρ b) (ρ c) (λ e → p (inj e))
                                            (λ e → q (inj e)) (λ e → r (inj e)))
                                 (Signs-oracle D))
                       (Signs-gᶜ ρ inj Bs))
             sum
  where
  f : Term _ → Term _
  f = mapTerm ρ inj

  D G : List (Term _)
  D = map f (map drawTerm (toList ds))
  G = map f (gTerms Bs)

  sum : ∀ z → ((z (ρ a) ∧ (z (ρ b) ∧ z (ρ c))) xor sumᵇ D z) xor sumᵇ G z ≡
              sumᵇ (map f (gTerms (block a b c p q r ds ∷ Bs))) z
  sum z = trans (xor-assoc (z (ρ a) ∧ (z (ρ b) ∧ z (ρ c))) (sumᵇ D z)
                           (sumᵇ G z))
    (cong ((z (ρ a) ∧ (z (ρ b) ∧ z (ρ c))) xor_)
          (sym (trans (cong (λ l → sumᵇ l z)
                            (map-++ f (map drawTerm (toList ds)) (gTerms Bs)))
                      (sumᵇ-++ D G z))))

-- On the two halves of the wires: g as drawn, on the first m, and the
-- tool's substitution of x_(m+i) for x_i, on the last m.

gˡ gʳ : List (Block d m) → CRK.Circuit (m ℕ+ m)
gˡ {m = m} = gᶜ (λ i → i ↑ˡ m) (λ {a} {b} → Fin.↑ˡ-injective m a b)
gʳ {m = m} = gᶜ (λ i → m ↑ʳ i) (λ {a} {b} → Fin.↑ʳ-injective m a b)

-- The tool's cTrans: a cz between x_i and x_(m+i) for every i < m.

cTᶜ : ∀ m → CRK.Circuit (m ℕ+ m)
cTᶜ m = oracle (xyTerms m)

-- The tool's oracles: g ++ cTrans is (-1)^f, and g′ ++ cTrans is
-- (-1)^{f̃}, g the sum of the drawn monomials.

Oᶠᵗ Oᵈᵗ : List (Block d m) → CRK.Circuit (m ℕ+ m)
Oᶠᵗ {m = m} Bs = gˡ Bs ++ cTᶜ m
Oᵈᵗ {m = m} Bs = gʳ Bs ++ cTᶜ m

Signs-Oᶠᵗ : (Bs : List (Block d m)) →
            Signs (Oᶠᵗ Bs) (sumᵇ (fTerms (gTerms Bs)))
Signs-Oᶠᵗ {m = m} Bs =
  Signs-cong (Signs-++ (Signs-gᶜ (λ i → i ↑ˡ m)
                                 (λ {a} {b} → Fin.↑ˡ-injective m a b) Bs)
                       (Signs-oracle (xyTerms m)))
             (λ z → sym (sumᵇ-++ (onLeft (gTerms Bs)) (xyTerms m) z))

Signs-Oᵈᵗ : (Bs : List (Block d m)) →
            Signs (Oᵈᵗ Bs) (sumᵇ (f̃Terms (gTerms Bs)))
Signs-Oᵈᵗ {m = m} Bs =
  Signs-cong (Signs-++ (Signs-gᶜ (λ i → m ↑ʳ i)
                                 (λ {a} {b} → Fin.↑ʳ-injective m a b) Bs)
                       (Signs-oracle (xyTerms m)))
             (λ z → trans (xor-comm (sumᵇ (onRight (gTerms Bs)) z)
                                    (sumᵇ (xyTerms m) z))
                          (sym (sumᵇ-++ (xyTerms m) (onRight (gTerms Bs)) z)))

norm-Oᶠᵗ : (Bs : List (Block d m)) → CRK.norm (Oᶠᵗ Bs) ≡ 0
norm-Oᶠᵗ {m = m} Bs = trans (norm-++ (gˡ Bs) (cTᶜ m))
  (cong₂ _ℕ+_ (norm-gᶜ (λ i → i ↑ˡ m) (λ {a} {b} → Fin.↑ˡ-injective m a b) Bs)
              (norm-oracle (xyTerms m)))

norm-Oᵈᵗ : (Bs : List (Block d m)) → CRK.norm (Oᵈᵗ Bs) ≡ 0
norm-Oᵈᵗ {m = m} Bs = trans (norm-++ (gʳ Bs) (cTᶜ m))
  (cong₂ _ℕ+_ (norm-gᶜ (λ i → m ↑ʳ i) (λ {a} {b} → Fin.↑ʳ-injective m a b) Bs)
              (norm-oracle (xyTerms m)))


------------------------------------------------------------------------
-- The circuit

-- The tool's hTrans, f = xTrans ++ g ++ cTrans ++ xTrans and
-- f′ = (subst sub g) ++ cTrans, over {H, X, CNOT, R_k, R_k†}.

hTˣ : ∀ m → Circuit (m ℕ+ m)
hTˣ m = map embed (hadamards (m ℕ+ m))

fˣ : Assign (m ℕ+ m) → List (Block d m) → Circuit (m ℕ+ m)
fˣ {m = m} s Bs =
  flipsˣ s ++ map embed (gˡ Bs) ++ map embed (cTᶜ m) ++ flipsˣ s

f′ˣ : List (Block d m) → Circuit (m ℕ+ m)
f′ˣ {m = m} Bs = map embed (gʳ Bs) ++ map embed (cTᶜ m)

-- hTrans ++ f ++ hTrans ++ f′ ++ hTrans.

HSᵗ : Assign (m ℕ+ m) → List (Block d m) → Circuit (m ℕ+ m)
HSᵗ {m = m} s Bs = hTˣ m ++ fˣ s Bs ++ hTˣ m ++ f′ˣ Bs ++ hTˣ m

-- Bracketed as the layers of HS: H^n, X^s O_f X^s, H^n, O_f̃, H^n.

private
  assoc5 : {A : Set} (a b c d e : List A) →
           a ++ (b ++ (c ++ (d ++ e))) ≡ (((a ++ b) ++ c) ++ d) ++ e
  assoc5 a b c d e = sym (trans (++-assoc ((a ++ b) ++ c) d e)
    (trans (++-assoc (a ++ b) c (d ++ e)) (++-assoc a b (c ++ (d ++ e)))))

HSᵗ-layers : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) →
             HSᵗ s Bs ≡
             (((hTˣ m ++ (flipsˣ s ++ (map embed (Oᶠᵗ Bs) ++ flipsˣ s))) ++
               hTˣ m) ++ map embed (Oᵈᵗ Bs)) ++ hTˣ m
HSᵗ-layers {m = m} s Bs =
  trans (cong₂ (λ F F′ → hTˣ m ++ F ++ hTˣ m ++ F′ ++ hTˣ m) eqF eqF′)
        (assoc5 (hTˣ m) (flipsˣ s ++ (map embed (Oᶠᵗ Bs) ++ flipsˣ s)) (hTˣ m)
                (map embed (Oᵈᵗ Bs)) (hTˣ m))
  where
  eqF : fˣ s Bs ≡ flipsˣ s ++ (map embed (Oᶠᵗ Bs) ++ flipsˣ s)
  eqF = cong (flipsˣ s ++_)
    (trans (sym (++-assoc (map embed (gˡ Bs)) (map embed (cTᶜ m)) (flipsˣ s)))
           (cong (_++ flipsˣ s) (sym (map-++ embed (gˡ Bs) (cTᶜ m)))))

  eqF′ : f′ˣ Bs ≡ map embed (Oᵈᵗ Bs)
  eqF′ = sym (map-++ embed (gʳ Bs) (cTᶜ m))

-- Its normalisation is 3n: the Hadamards of the three layers.

norm-HSᵗ : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) →
           norm (HSᵗ s Bs) ≡ hs-norm (m ℕ+ m) ℕ+ 0
norm-HSᵗ {m = m} s Bs =
  trans (norm-++ˣ (hTˣ m) (fˣ s Bs ++ hTˣ m ++ f′ˣ Bs ++ hTˣ m))
  (trans (cong₂ _ℕ+_ nH
    (trans (norm-++ˣ (fˣ s Bs) (hTˣ m ++ f′ˣ Bs ++ hTˣ m))
    (cong₂ _ℕ+_ nF
      (trans (norm-++ˣ (hTˣ m) (f′ˣ Bs ++ hTˣ m))
      (cong₂ _ℕ+_ nH
        (trans (norm-++ˣ (f′ˣ Bs) (hTˣ m)) (cong₂ _ℕ+_ nF′ nH)))))))
  (arith (m ℕ+ m)))
  where
  nH : norm (hTˣ m) ≡ m ℕ+ m
  nH = trans (norm-embed (hadamards (m ℕ+ m))) (norm-hadamards (m ℕ+ m))

  nE : (C : CRK.Circuit (m ℕ+ m)) → CRK.norm C ≡ 0 → norm (map embed C) ≡ 0
  nE C e = trans (norm-embed C) e

  nF : norm (fˣ s Bs) ≡ 0
  nF = trans (norm-++ˣ (flipsˣ s) _)
    (cong₂ _ℕ+_ (norm-flipsˣ s)
      (trans (norm-++ˣ (map embed (gˡ Bs)) _)
        (cong₂ _ℕ+_ (nE (gˡ Bs) (norm-gᶜ _ _ Bs))
          (trans (norm-++ˣ (map embed (cTᶜ m)) (flipsˣ s))
                 (cong₂ _ℕ+_ (nE (cTᶜ m) (norm-oracle (xyTerms m)))
                             (norm-flipsˣ s))))))

  nF′ : norm (f′ˣ Bs) ≡ 0
  nF′ = trans (norm-++ˣ (map embed (gʳ Bs)) (map embed (cTᶜ m)))
    (cong₂ _ℕ+_ (nE (gʳ Bs) (norm-gᶜ _ _ Bs))
                (nE (cTᶜ m) (norm-oracle (xyTerms m))))

  arith : ∀ a → a ℕ+ (0 ℕ+ (a ℕ+ (0 ℕ+ a))) ≡
                ((((a ℕ+ 0) ℕ+ a) ℕ+ 0) ℕ+ a) ℕ+ 0
  arith = solve 1 (λ a → a :+ (con 0 :+ (a :+ (con 0 :+ a))) :=
                         ((((a :+ con 0) :+ a) :+ con 0) :+ a) :+ con 0) refl


------------------------------------------------------------------------
-- The circuit is the composite HS

-- Each layer simulates a layer of PathSum.HiddenShift's HS.

Sim-HSᵗ : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) →
          Sim (applyᴬ (HSᵗ s Bs)) (HS (sumᴾ (gTerms Bs)) s) 0
Sim-HSᵗ {m = m} s Bs =
  subst (λ C → Sim (applyᴬ C) (HS (sumᴾ (gTerms Bs)) s) 0)
        (sym (HSᵗ-layers s Bs))
    (Sim-++ˣ (((Hn ++ X) ++ Hn) ++ D) Hn
      (Sim-++ˣ ((Hn ++ X) ++ Hn) D
        (Sim-++ˣ (Hn ++ X) Hn
          (Sim-++ˣ Hn X SH
            (Sim-shiftedˣ s (Signs-Oᶠᵗ Bs) (mmᴾ (sumᴾ (gTerms Bs)))
                          (bool-f (gTerms Bs))))
          SH)
        (Sim-embed (Oᵈᵗ Bs)
          (Sim-signs (Signs-Oᵈᵗ Bs) (dualᴾ (sumᴾ (gTerms Bs)))
                     (bool-f̃ (gTerms Bs)))))
      SH)
  where
  Hn X D : Circuit (m ℕ+ m)
  Hn = hTˣ m
  X  = flipsˣ s ++ (map embed (Oᶠᵗ Bs) ++ flipsˣ s)
  D  = map embed (Oᵈᵗ Bs)

  SH : Sim (applyᴬ Hn) (Hᴾ {m ℕ+ m}) 0
  SH = Sim-embed (hadamards (m ℕ+ m)) (Sim-hadamards (m ℕ+ m))

-- So it is the composite, in the sense of definition 2.3, for every
-- m, every shift and every draw.

hidden-shift-tool-≋ : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) →
                      ⟦ HSᵗ s Bs ⟧ ≋ HS (sumᴾ (gTerms Bs)) s
hidden-shift-tool-≋ s Bs =
  Sim-≋ˣ (HSᵗ s Bs) (HS (sumᴾ (gTerms Bs)) s) (Sim-HSᵗ s Bs) (norm-HSᵗ s Bs)

-- From |0⟩ it reaches |s⟩, with amplitude √2^K before the
-- normalisation 1/√2^K, K = norm (HSᵗ s Bs) = 3n, and nothing else.

hidden-shift-tool : (s : Assign (m ℕ+ m)) (Bs : List (Block d m))
                    (z : Assign (m ℕ+ m)) →
                    amp ⟦ HSᵗ s Bs ⟧ 0ᵃ z ≐
                    (if same s z then scale (norm (HSᵗ s Bs)) (zpow 0ℤ)
                     else 0ᴬ)
hidden-shift-tool {m = m} s Bs z i =
  trans (Sim-circuitˣ (HSᵗ s Bs) (Sim-HSᵗ s Bs) 0ᵃ z i)
    (trans (hidden-shift (sumᴾ (gTerms Bs)) s z i) (pick (same s z) i))
  where
  pick : ∀ b → (if b then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ) else 0ᴬ) ≐
               (if b then scale (norm (HSᵗ s Bs)) (zpow 0ℤ) else 0ᴬ)
  pick true  = scale-exp (zpow 0ℤ)
    (sym (trans (norm-HSᵗ s Bs) (+-identityʳ (hs-norm (m ℕ+ m)))))
  pick false _ = refl

-- The circuit's path-sum on |0⟩ is the specification |x⟩ ↦ |s⟩ ...

hidden-shift-tool-at0 : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) →
                        at0 ⟦ HSᵗ s Bs ⟧ ≋ specᴾ s
hidden-shift-tool-at0 s Bs x z i = trans (amp-at0 ⟦ HSᵗ s Bs ⟧ x z i)
  (trans (hidden-shift-tool s Bs z i)
    (sym (trans (scale-map (norm (HSᵗ s Bs)) (amp-specᴾ s x z) i)
                (pick (same s z) i))))
  where
  pick : ∀ b → scale (norm (HSᵗ s Bs)) (if b then 1ᴬ else 0ᴬ) ≐
               (if b then scale (norm (HSᵗ s Bs)) (zpow 0ℤ) else 0ᴬ)
  pick true  l = refl
  pick false l = scale-0ᴬ (norm (HSᵗ s Bs)) l

-- ... on every input prepared in |0⟩ (PathSum.Ancilla.Register) ...

hidden-shift-tool-register : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) →
                             ⟦ HSᵗ s Bs ⟧ ≋⟨ allMask (m ℕ+ m) ⟩₀ specᴾ s
hidden-shift-tool-register s Bs x z p i =
  trans (amp-input ⟦ HSᵗ s Bs ⟧ (λ j → p j refl) z i)
        (trans (sym (amp-at0 ⟦ HSᵗ s Bs ⟧ x z i))
               (hidden-shift-tool-at0 s Bs x z i))

-- ... and with every input read as 0 its path-sum is the
-- specification: what the tool's verifyHiddenShift checks, against
-- hiddenShiftSpec with every input False.

hidden-shift-tool-set0 : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) →
                         set0ᶜ (allMask (m ℕ+ m)) ⟦ HSᵗ s Bs ⟧ ≋ specᴾ s
hidden-shift-tool-set0 {m = m} s Bs =
  ≋⟨⟩₀-set0ᶜ (allMask (m ℕ+ m)) ⟦ HSᵗ s Bs ⟧ (specᴾ s)
    (hidden-shift-tool-register s Bs)
    (λ x z l → trans (amp-specᴾ s _ z l) (sym (amp-specᴾ s x z l)))

-- Every complete reduction of it by figure 2's rules, at any path
-- variables, ends at |x⟩ ↦ |s⟩ syntactically.

tool-reduces : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) {k′ : ℕ}
               {ζ : PathSum (m ℕ+ m) k′ 0} →
               at0 ⟦ HSᵗ s Bs ⟧ ⟶ᶠ* ζ →
               (k′ ≡ 0) ×
               (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
               (phase ζ ≈[ pow M ] 0ᴾ)
tool-reduces s Bs {k′} {ζ} steps = spec-only-if s ζ
  (≋-trans {ξ = ζ} {ζ = at0 ⟦ HSᵗ s Bs ⟧} {χ = specᴾ s}
    (≋-sym {ξ = at0 ⟦ HSᵗ s Bs ⟧} {ζ = ζ} (⟶ᶠ*-sound steps))
    (hidden-shift-tool-at0 s Bs))

-- So it is PathSum.HiddenShift.Circuit's circuit of figure 3(a) on
-- the same monomials -- there with X written H R₁ H, and the tool's
-- ccz replaced by Gates's CCZᶜ -- up to ≋.

tool-≋-figure3a : (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) →
                  ⟦ HSᵗ s Bs ⟧ ≋ CRK.⟦ HSᶜ (gTerms Bs) s ⟧
tool-≋-figure3a s Bs =
  ≋-trans {ξ = ⟦ HSᵗ s Bs ⟧} {ζ = HS (sumᴾ (gTerms Bs)) s}
          {χ = CRK.⟦ HSᶜ (gTerms Bs) s ⟧}
    (hidden-shift-tool-≋ s Bs)
    (≋-sym {ξ = CRK.⟦ HSᶜ (gTerms Bs) s ⟧} {ζ = HS (sumᴾ (gTerms Bs)) s}
           (hidden-shift-circuit-≋ (gTerms Bs) s))
