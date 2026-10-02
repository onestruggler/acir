------------------------------------------------------------------------
-- Presentations of groups
--
-- The symbolic shift benchmark as the paper's tool generates it,
-- correct for every random draw (Amy, QPL 2018, section 5.2 and
-- table 2)
--
-- The tool's hiddenShiftQuantum (src/Feynman/Verification/SOP.hs as
-- of the paper) is its hiddenShift with the shift held in a second
-- register y of n qubits: its X^s is replaced by
--
--    xTrans = [CNOT y_i x_i | i <- [0 .. n − 1]] ,
--
-- and the oracles are drawn as before (PathSum.HiddenShift.Tool's
-- Block).  Here (SSᶜᵗ Bs) is that circuit over {H, CNOT, R_k, R_k†},
-- the data register x on the first n wires and y on the last n, built
-- from PathSum.HiddenShift.Symbolic's CNOT layer (cnots) and the data
-- register's circuits placed with PathSum.HiddenShift.Gates's upper,
-- and SSᵗ Bs the same over {H, X, CNOT, R_k, R_k†} (it has no X).
-- PathSum.HiddenShift.Feynman shows it is the tool's list gate for
-- gate.
--
-- The argument is PathSum.HiddenShift.Symbolic's, with the tool's
-- oracles (Slices-SSᵗ, Sim-sliceᵗ): the shift register only controls,
-- so on the slice with the shift register at v the circuit is
-- PathSum.HiddenShift's composite HS g v, g the sum of the drawn
-- monomials, and at every input (symbolic-shift-tool)
--
--    amp (|x⟩|t⟩ → |u⟩|v⟩) = [t = v] · amp_{HS g v}(|x⟩ → |u⟩) .
--
-- With x = 0 this is the tool's specification hiddenShiftQuantumSpec,
-- |0⟩|y⟩ ↦ |y⟩|y⟩ for every y (symbolic-shift-tool-0); as a path-sum,
-- with the data register prepared in |0⟩ (PathSum.Ancilla.Register),
-- it is Symbolic's specSᴾ, |x, y⟩ ↦ |y, y⟩ with y the input variables
-- (symbolic-shift-tool-≋), and with the data register read as the
-- constant 0 the path-sums are ≋ (symbolic-shift-tool-set0) -- the
-- statement the tool's verifyHiddenShiftQuantum checks.  The circuit
-- has 3n Hadamards (norm-SSᵗ), as in table 2, and from every |x⟩|t⟩
-- to every |u⟩|v⟩ the amplitude of PathSum.HiddenShift.Symbolic's
-- circuit of figure 3(b) on the same monomials (tool-figure3b).  With
-- the data register read as 0 its path-sum reduces by figure 2's rules,
-- in exactly 3n steps, to |x, y⟩ ↦ |y, y⟩, and every complete
-- reduction ends there (PathSum.HiddenShift.ToolExists).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.ToolSymbolic (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; _∧_; if_then_else_)
open import Data.Bool.Properties using (∧-identityʳ; ∧-zeroʳ)
open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (0ℤ)
open import Data.Integer.Properties using (*-zeroˡ)
open import Data.List.Base using (List; _++_; map)
open import Data.List.Properties using (++-assoc)
open import Data.Nat.Base using (suc) renaming (_+_ to _ℕ+_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import PathSum.AmpLinear M₀ using (·ᴬ-linear; scale-exp)
open import PathSum.Ancilla.Register M₀ using
  (Prepared; mask; set0ᶜ; amp-input; _≋⟨_⟩₀_; ≋⟨⟩₀-set0ᶜ)
open import PathSum.Assign using (same; same-true; same-≗)
open import PathSum.Base using (PathSum)
open import PathSum.CircuitSemantics M₀ using (Column; δ; δ-resp)
open import PathSum.Compose.Properties M₀ using (applyᴾ; applyᴾ-linear)
open import PathSum.Cyclotomic M₀ using
  (0ᴬ; _≐_; zpow; scale; scale-map)
open import PathSum.Denotation M₀ using (Assign; amp; amp-≗; _≋_)
open import PathSum.HiddenShift M₀ using
  (mmᴾ; dualᴾ; HS; hs-norm; hidden-shift; scale-0ᴬ)
open import PathSum.HiddenShift.Circuit M₀ using
  (sumᴾ; xyTerms; bool-f; bool-f̃)
open import PathSum.HiddenShift.Gates M₀ using
  (upper; upper-++; norm-upper; norm-oracle)
open import PathSum.HiddenShift.Layers M₀ using
  (hadamards; norm-hadamards; Sim; simulates; Sim-∘; Sim-δ; Sim-hadamards;
   Sim-signs)
open import PathSum.HiddenShift.LayersX M₀ using (amp-embed)
open import PathSum.HiddenShift.Sign M₀ using (1ᴬ)
open import PathSum.HiddenShift.Symbolic M₀ using
  (cnots; norm-cnots; Slices; on-slices; slice-cong; Slices-++; Slices-upper;
   shifted; Slices-shifted; Sim-slice-shifted; same-⧺; specSᴾ; amp-specSᴾ;
   dataMask; ⧺-cong₂; SSᶜ; symbolic-shift)
open import PathSum.HiddenShift.Tool M₀ using
  (Block; gTerms; gˡ; gʳ; cTᶜ; Oᶠᵗ; Oᵈᵗ; Signs-Oᶠᵗ; Signs-Oᵈᵗ; norm-gᶜ)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⧺_; ⧺-↑ˡ; ⧺-↑ʳ; ⧺-split; rhalf)

open +-*-Solver using (solve; con; _:+_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

import PathSum.CRK.Circuit
import PathSum.CRK.WithX

private
  module CRK = PathSum.CRK.Circuit M
  module Wˣ  = PathSum.CRK.WithX M₀

open import PathSum.CRK.Adjoint M using (norm-++)
open import PathSum.CRK.Semantics M₀ using (applyᴬ; prop-2-10)

private
  variable
    m d : ℕ


------------------------------------------------------------------------
-- The circuit

-- n = 2m data qubits x, then n shift qubits y.

private
  W : ℕ → ℕ
  W m = (m ℕ+ m) ℕ+ (m ℕ+ m)

-- The tool's xTrans, CNOT y_i x_i for i = 0 … n − 1, and hTrans on the
-- data register.

xTˢ hTˢ : ∀ m → CRK.Circuit (W m)
xTˢ m = cnots {m ℕ+ m} {m ℕ+ m} (λ i → i)
hTˢ m = upper (m ℕ+ m) (hadamards (m ℕ+ m))

-- f = xTrans ++ g ++ cTrans ++ xTrans, f′ = (subst sub g) ++ cTrans,
-- g and cTrans on the data register.

fˢ f′ˢ : List (Block d m) → CRK.Circuit (W m)
fˢ {m = m} Bs = xTˢ m ++ upper (m ℕ+ m) (gˡ Bs) ++
                upper (m ℕ+ m) (cTᶜ m) ++ xTˢ m
f′ˢ {m = m} Bs = upper (m ℕ+ m) (gʳ Bs) ++ upper (m ℕ+ m) (cTᶜ m)

-- hTrans ++ f ++ hTrans ++ f′ ++ hTrans, over {H, CNOT, R_k, R_k†} and
-- over {H, X, CNOT, R_k, R_k†}.

SSᶜᵗ : List (Block d m) → CRK.Circuit (W m)
SSᶜᵗ {m = m} Bs = hTˢ m ++ fˢ Bs ++ hTˢ m ++ f′ˢ Bs ++ hTˢ m

SSᵗ : List (Block d m) → Wˣ.Circuit (W m)
SSᵗ Bs = map Wˣ.embed (SSᶜᵗ Bs)

-- Bracketed as the layers of PathSum.HiddenShift.Symbolic's SSᶜ.

private
  assoc5 : {A : Set} (a b c d e : List A) →
           a ++ (b ++ (c ++ (d ++ e))) ≡ (((a ++ b) ++ c) ++ d) ++ e
  assoc5 a b c d e = sym (trans (++-assoc ((a ++ b) ++ c) d e)
    (trans (++-assoc (a ++ b) c (d ++ e)) (++-assoc a b (c ++ (d ++ e)))))

SSᶜᵗ-layers : (Bs : List (Block d m)) →
              SSᶜᵗ Bs ≡
              (((hTˢ m ++ (xTˢ m ++ (upper (m ℕ+ m) (Oᶠᵗ Bs) ++ xTˢ m))) ++
                hTˢ m) ++ upper (m ℕ+ m) (Oᵈᵗ Bs)) ++ hTˢ m
SSᶜᵗ-layers {m = m} Bs =
  trans (cong₂ (λ F F′ → hTˢ m ++ F ++ hTˢ m ++ F′ ++ hTˢ m) eqF eqF′)
        (assoc5 (hTˢ m) (xTˢ m ++ (upper n (Oᶠᵗ Bs) ++ xTˢ m)) (hTˢ m)
                (upper n (Oᵈᵗ Bs)) (hTˢ m))
  where
  n : ℕ
  n = m ℕ+ m

  eqF : fˢ Bs ≡ xTˢ m ++ (upper n (Oᶠᵗ Bs) ++ xTˢ m)
  eqF = cong (xTˢ m ++_)
    (trans (sym (++-assoc (upper n (gˡ Bs)) (upper n (cTᶜ m)) (xTˢ m)))
           (cong (_++ xTˢ m) (sym (upper-++ n (gˡ Bs) (cTᶜ m)))))

  eqF′ : f′ˢ Bs ≡ upper n (Oᵈᵗ Bs)
  eqF′ = sym (upper-++ n (gʳ Bs) (cTᶜ m))

-- 3n Hadamards.

norm-SSᶜᵗ : (Bs : List (Block d m)) → CRK.norm (SSᶜᵗ Bs) ≡ hs-norm (m ℕ+ m)
norm-SSᶜᵗ {m = m} Bs =
  trans (norm-++ (hTˢ m) (fˢ Bs ++ hTˢ m ++ f′ˢ Bs ++ hTˢ m))
  (trans (cong₂ _ℕ+_ nA
    (trans (norm-++ (fˢ Bs) (hTˢ m ++ f′ˢ Bs ++ hTˢ m))
    (cong₂ _ℕ+_ nF
      (trans (norm-++ (hTˢ m) (f′ˢ Bs ++ hTˢ m))
      (cong₂ _ℕ+_ nA
        (trans (norm-++ (f′ˢ Bs) (hTˢ m)) (cong₂ _ℕ+_ nF′ nA)))))))
  (arith n))
  where
  n : ℕ
  n = m ℕ+ m

  nA : CRK.norm (hTˢ m) ≡ n
  nA = trans (norm-upper n (hadamards n)) (norm-hadamards n)

  nX : CRK.norm (xTˢ m) ≡ 0
  nX = norm-cnots {n} {n} (λ i → i)

  nU : (C : CRK.Circuit n) → CRK.norm C ≡ 0 → CRK.norm (upper n C) ≡ 0
  nU C e = trans (norm-upper n C) e

  nF : CRK.norm (fˢ Bs) ≡ 0
  nF = trans (norm-++ (xTˢ m) _)
    (cong₂ _ℕ+_ nX
      (trans (norm-++ (upper n (gˡ Bs)) _)
        (cong₂ _ℕ+_ (nU (gˡ Bs) (norm-gᶜ _ _ Bs))
          (trans (norm-++ (upper n (cTᶜ m)) (xTˢ m))
                 (cong₂ _ℕ+_ (nU (cTᶜ m) (norm-oracle (xyTerms m))) nX)))))

  nF′ : CRK.norm (f′ˢ Bs) ≡ 0
  nF′ = trans (norm-++ (upper n (gʳ Bs)) (upper n (cTᶜ m)))
    (cong₂ _ℕ+_ (nU (gʳ Bs) (norm-gᶜ _ _ Bs))
                (nU (cTᶜ m) (norm-oracle (xyTerms m))))

  arith : ∀ a → a ℕ+ (0 ℕ+ (a ℕ+ (0 ℕ+ a))) ≡ (((a ℕ+ 0) ℕ+ a) ℕ+ 0) ℕ+ a
  arith = solve 1 (λ a → a :+ (con 0 :+ (a :+ (con 0 :+ a))) :=
                         (((a :+ con 0) :+ a) :+ con 0) :+ a) refl

norm-SSᵗ : (Bs : List (Block d m)) → Wˣ.norm (SSᵗ Bs) ≡ hs-norm (m ℕ+ m)
norm-SSᵗ Bs = trans (Wˣ.norm-embed (SSᶜᵗ Bs)) (norm-SSᶜᵗ Bs)


------------------------------------------------------------------------
-- Slice by slice

-- What the circuit does to the slice at v.

slice-opᵗ : List (Block d m) → Assign (m ℕ+ m) → Column (m ℕ+ m) →
            Column (m ℕ+ m)
slice-opᵗ {m = m} Bs v ψ =
  applyᴬ (hadamards (m ℕ+ m))
    (applyᴬ (Oᵈᵗ Bs)
      (applyᴬ (hadamards (m ℕ+ m))
        (shifted v (Oᶠᵗ Bs) (applyᴬ (hadamards (m ℕ+ m)) ψ))))

Slices-SSᵗ : (Bs : List (Block d m)) → Slices (SSᶜᵗ Bs) (slice-opᵗ Bs)
Slices-SSᵗ {m = m} Bs =
  subst (λ C → Slices C (slice-opᵗ Bs)) (sym (SSᶜᵗ-layers Bs))
    (Slices-++ (((A ++ X) ++ A) ++ D) A
      (Slices-++ ((A ++ X) ++ A) D
        (Slices-++ (A ++ X) A
          (Slices-++ A X (Slices-upper (hadamards n))
                         (Slices-shifted (Oᶠᵗ Bs)))
          (Slices-upper (hadamards n)))
        (Slices-upper (Oᵈᵗ Bs)))
      (Slices-upper (hadamards n)))
  where
  n : ℕ
  n = m ℕ+ m

  A D X : CRK.Circuit (n ℕ+ n)
  A = hTˢ m
  D = upper n (Oᵈᵗ Bs)
  X = xTˢ m ++ (upper n (Oᶠᵗ Bs) ++ xTˢ m)

-- On the slice at v it is the composite HS g v.

Sim-sliceᵗ : (Bs : List (Block d m)) (v : Assign (m ℕ+ m)) →
             Sim (slice-opᵗ Bs v) (HS (sumᴾ (gTerms Bs)) v) 0
Sim-sliceᵗ {m = m} Bs v =
  Sim-∘ (Sim-∘ (Sim-∘ (Sim-∘ (Sim-hadamards n)
                               (Sim-slice-shifted v (Signs-Oᶠᵗ Bs)
                                                  (mmᴾ (sumᴾ (gTerms Bs)))
                                                  (bool-f (gTerms Bs))))
                       (Sim-hadamards n))
               (Sim-signs (Signs-Oᵈᵗ Bs) (dualᴾ (sumᴾ (gTerms Bs)))
                          (bool-f̃ (gTerms Bs))))
        (Sim-hadamards n)
  where
  n : ℕ
  n = m ℕ+ m


------------------------------------------------------------------------
-- The circuit's amplitudes

-- A simulating operator sends the zero column to zero.

private
  applyᴾ-0 : ∀ {n k′ m′} (ξ : PathSum n k′ m′) (z : Assign n) →
             applyᴾ ξ (λ _ → 0ᴬ) z ≐ 0ᴬ
  applyᴾ-0 ξ z i = trans (applyᴾ-linear (·ᴬ-linear 0ℤ) ξ (λ _ → 0ᴬ) z i)
                         (*-zeroˡ (applyᴾ ξ (λ _ → 0ᴬ) z i))

  Sim-0 : ∀ {n k′ m′} {L : Column n → Column n} {ξ : PathSum n k′ m′} {e : ℕ} →
          Sim L ξ e → ∀ z → L (λ _ → 0ᴬ) z ≐ 0ᴬ
  Sim-0 {ξ = ξ} {e} S z i =
    trans (simulates S (λ _ → 0ᴬ) (λ _ _ _ _ → refl) z i)
          (trans (scale-map e (applyᴾ-0 ξ z) i) (scale-0ᴬ e i))

-- Over {H, CNOT, R_k, R_k†}: Σ_t HS(g, t) ⊗ |t⟩⟨t|.

symbolic-shift-toolᶜ : (Bs : List (Block d m)) (x t u v : Assign (m ℕ+ m)) →
                       amp (CRK.⟦ SSᶜᵗ Bs ⟧) (x ⧺ t) (u ⧺ v) ≐
                       (if same t v then amp (HS (sumᴾ (gTerms Bs)) v) x u
                        else 0ᴬ)
symbolic-shift-toolᶜ {m = m} Bs x t u v i =
  trans (prop-2-10 (SSᶜᵗ Bs) (x ⧺ t) (u ⧺ v) i)
    (trans (on-slices (Slices-SSᵗ Bs) (δ (x ⧺ t)) (δ-resp (x ⧺ t)) u v i)
           (pick (same t v) refl i))
  where
  σ : Column (m ℕ+ m)
  σ u′ = δ (x ⧺ t) (u′ ⧺ v)

  σ-guard : ∀ u′ → σ u′ ≐ (if same x u′ ∧ same t v then zpow 0ℤ else 0ᴬ)
  σ-guard u′ l = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) l)
                      (same-⧺ x u′ t v)

  pick : ∀ b → same t v ≡ b →
         slice-opᵗ Bs v σ u ≐
         (if b then amp (HS (sumᴾ (gTerms Bs)) v) x u else 0ᴬ)
  pick true  e l = trans
    (slice-cong (Slices-SSᵗ Bs) v {σ} {δ x} (λ u′ l′ → trans (σ-guard u′ l′)
      (cong (λ b → (if b then zpow 0ℤ else 0ᴬ) l′)
            (trans (cong (same x u′ ∧_) e) (∧-identityʳ (same x u′))))) u l)
    (Sim-δ (Sim-sliceᵗ Bs v) x u l)
  pick false e l = trans
    (slice-cong (Slices-SSᵗ Bs) v {σ} {λ _ → 0ᴬ}
                (λ u′ l′ → trans (σ-guard u′ l′)
      (cong (λ b → (if b then zpow 0ℤ else 0ᴬ) l′)
            (trans (cong (same x u′ ∧_) e) (∧-zeroʳ (same x u′))))) u l)
    (Sim-0 (Sim-sliceᵗ Bs v) u l)

-- The same over {H, X, CNOT, R_k, R_k†}.

symbolic-shift-tool : (Bs : List (Block d m)) (x t u v : Assign (m ℕ+ m)) →
                      amp (Wˣ.⟦ SSᵗ Bs ⟧) (x ⧺ t) (u ⧺ v) ≐
                      (if same t v then amp (HS (sumᴾ (gTerms Bs)) v) x u
                       else 0ᴬ)
symbolic-shift-tool Bs x t u v i =
  trans (amp-embed (SSᶜᵗ Bs) (x ⧺ t) (u ⧺ v) i)
        (symbolic-shift-toolᶜ Bs x t u v i)

-- The tool's specification |0⟩|y⟩ ↦ |y⟩|y⟩, for every y: the only
-- output reached is |y⟩|y⟩, with amplitude √2^K before the
-- normalisation 1/√2^K, K = 3n.

symbolic-shift-tool-0 : (Bs : List (Block d m)) (s : Assign (m ℕ+ m))
                        (z : Assign ((m ℕ+ m) ℕ+ (m ℕ+ m))) →
                        amp (Wˣ.⟦ SSᵗ Bs ⟧) (0ᵃ {m ℕ+ m} ⧺ s) z ≐
                        (if same (s ⧺ s) z
                         then scale (Wˣ.norm (SSᵗ Bs)) (zpow 0ℤ) else 0ᴬ)
symbolic-shift-tool-0 {m = m} Bs s z i =
  trans (amp-≗ Wˣ.⟦ SSᵗ Bs ⟧ (0ᵃ {m ℕ+ m} ⧺ s) (λ j → sym (⧺-split n n z j)) i)
    (trans (symbolic-shift-tool Bs 0ᵃ s u v i)
      (trans (pick (same s v) refl i)
             (cong (λ b → (if b then scale (Wˣ.norm (SSᵗ Bs)) (zpow 0ℤ)
                           else 0ᴬ) i)
                   (sym (trans (same-≗ {x = s ⧺ s} {x′ = s ⧺ s}
                                       {z = z} {z′ = u ⧺ v} (λ _ → refl)
                                       (λ j → sym (⧺-split n n z j)))
                               (same-⧺ s u s v))))))
  where
  n : ℕ
  n = m ℕ+ m

  u v : Assign n
  u j = z (j ↑ˡ n)
  v j = z (n ↑ʳ j)

  pick : ∀ b → same s v ≡ b →
         (if b then amp (HS (sumᴾ (gTerms Bs)) v) 0ᵃ u else 0ᴬ) ≐
         (if same s u ∧ b then scale (Wˣ.norm (SSᵗ Bs)) (zpow 0ℤ) else 0ᴬ)
  pick false e l = cong (λ c → (if c then scale (Wˣ.norm (SSᵗ Bs)) (zpow 0ℤ)
                                else 0ᴬ) l)
                        (sym (∧-zeroʳ (same s u)))
  pick true  e l = trans (hidden-shift (sumᴾ (gTerms Bs)) v u l)
    (trans (cong (λ c → (if c then scale (hs-norm n) (zpow 0ℤ) else 0ᴬ) l)
                 (trans (same-≗ {x = v} {x′ = s} {z = u} {z′ = u}
                                (λ j → sym (same-true s v e j)) (λ _ → refl))
                        (sym (∧-identityʳ (same s u)))))
           (fix (same s u ∧ true) l))
    where
    fix : ∀ c → (if c then scale (hs-norm n) (zpow 0ℤ) else 0ᴬ) ≐
                (if c then scale (Wˣ.norm (SSᵗ Bs)) (zpow 0ℤ) else 0ᴬ)
    fix true  = scale-exp (zpow 0ℤ) (sym (norm-SSᵗ Bs))
    fix false _ = refl

-- A prepared input is 0 followed by its second register.

private
  prepared-split : ∀ {n} (x : Assign (n ℕ+ n)) → Prepared (dataMask n) x →
                   ∀ j → x j ≡ (0ᵃ {n} ⧺ rhalf {n} x) j
  prepared-split {n} x p j = trans (sym (⧺-split n n x j))
    (⧺-cong₂ {a = λ i → x (i ↑ˡ n)} {a′ = 0ᵃ {n}}
             {b = rhalf {n} x} {b′ = rhalf {n} x}
             (λ i → p (i ↑ˡ n) (⧺-↑ˡ (λ (_ : Fin n) → true)
                                     (λ (_ : Fin n) → false) i))
             (λ _ → refl) j)

-- With the data register prepared in |0⟩, the circuit is
-- |x, y⟩ ↦ |y, y⟩, the shift being the input variables of the second
-- register.

symbolic-shift-tool-≋ : (Bs : List (Block d m)) →
                        Wˣ.⟦ SSᵗ Bs ⟧ ≋⟨ dataMask (m ℕ+ m) ⟩₀ specSᴾ (m ℕ+ m)
symbolic-shift-tool-≋ {m = m} Bs x z p i =
  trans (amp-input Wˣ.⟦ SSᵗ Bs ⟧ (prepared-split {m ℕ+ m} x p) z i)
    (trans (symbolic-shift-tool-0 Bs (rhalf {m ℕ+ m} x) z i)
      (sym (trans (scale-map (Wˣ.norm (SSᵗ Bs))
                             (amp-specSᴾ (m ℕ+ m) x z) i)
                  (pick (same (rhalf {m ℕ+ m} x ⧺ rhalf {m ℕ+ m} x) z) i))))
  where
  pick : ∀ b → scale (Wˣ.norm (SSᵗ Bs)) (if b then 1ᴬ else 0ᴬ) ≐
               (if b then scale (Wˣ.norm (SSᵗ Bs)) (zpow 0ℤ) else 0ᴬ)
  pick true  l = refl
  pick false l = scale-0ᴬ (Wˣ.norm (SSᵗ Bs)) l

-- With the data register read as 0, the path-sums are equivalent: the
-- statement of the tool's verifyHiddenShiftQuantum, against
-- hiddenShiftQuantumSpec.

symbolic-shift-tool-set0 : (Bs : List (Block d m)) →
                           set0ᶜ (dataMask (m ℕ+ m)) Wˣ.⟦ SSᵗ Bs ⟧ ≋
                           specSᴾ (m ℕ+ m)
symbolic-shift-tool-set0 {m = m} Bs =
  ≋⟨⟩₀-set0ᶜ (dataMask n) Wˣ.⟦ SSᵗ Bs ⟧ (specSᴾ n)
    (symbolic-shift-tool-≋ Bs)
    (λ x z l → trans (amp-specSᴾ n (mask (dataMask n) x) z l)
      (trans (cong (λ b → (if b then 1ᴬ else 0ᴬ) l)
                   (same-≗ {x = rhalf {n} (mask (dataMask n) x) ⧺
                                rhalf {n} (mask (dataMask n) x)}
                           {x′ = rhalf {n} x ⧺ rhalf {n} x} {z = z} {z′ = z}
                           (⧺-cong₂ (keep x) (keep x)) (λ _ → refl)))
             (sym (amp-specSᴾ n x z l))))
  where
  n : ℕ
  n = m ℕ+ m

  -- The mask leaves the second register alone.
  keep : (x : Assign (n ℕ+ n)) →
         ∀ i → mask (dataMask n) x (n ↑ʳ i) ≡ x (n ↑ʳ i)
  keep x i = cong (λ b → if b then false else x (n ↑ʳ i))
                  (⧺-↑ʳ (λ (_ : Fin n) → true) (λ (_ : Fin n) → false) i)

-- So from every |x⟩|t⟩ to every |u⟩|v⟩ it has the amplitude of
-- PathSum.HiddenShift.Symbolic's circuit of figure 3(b) on the same
-- monomials.

tool-figure3b : (Bs : List (Block d m)) (x t u v : Assign (m ℕ+ m)) →
                amp (Wˣ.⟦ SSᵗ Bs ⟧) (x ⧺ t) (u ⧺ v) ≐
                amp (CRK.⟦ SSᶜ (gTerms Bs) ⟧) (x ⧺ t) (u ⧺ v)
tool-figure3b Bs x t u v i =
  trans (symbolic-shift-tool Bs x t u v i)
        (sym (symbolic-shift (gTerms Bs) x t u v i))
