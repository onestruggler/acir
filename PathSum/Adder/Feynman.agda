------------------------------------------------------------------------
-- Presentations of groups
--
-- The paper's adder exactly as its tool builds it, uncomputation
-- included, verified for every n (Amy, QPL 2018, section 5.2 and
-- table 2)
--
-- The paper's tool, Feynman (github.com/meamy/feynman), builds the
-- adder it verified by carryRipple, in src/Feynman/Verification/SOP.hs:
--
--    carryRipple n a b c = compute ++ copy ++ dagger compute
--
-- where compute is already over Clifford+T -- each Toffoli gate of the
-- netlist written out by the tool's sixteen-gate toffoli
-- (PathSum.Toffoli.Depth3) -- and dagger = reverse . map daggerGate
-- (src/Feynman/Core.hs) runs the gates last to first, T and T†
-- swapped.  PathSum.CRK.Adjoint's _† is that operation on circuits
-- over {H, CNOT, R_k, R_k†}, so the tool's circuit is, literally,
--
--    feynmanᶜ L = expand₃ compute ++ expand₃ copy ++ (expand₃ compute)†
--
-- on any layout L of the tool's wires (PathSum.Adder.CarryRipple),
-- Feynmanᶜ m on the tool's own (n = m + 1).  Its uncompute half is the
-- netlist's compute reversed, each Toffoli gate written out by the
-- adjoint of the tool's Toffoli circuit, tof₃† c₁ c₂ t = (tof₃ c₁ c₂ t)†,
-- the tool's dagger (toffoli x y z) (†-expand₃, feynmanᶜ-blocks) --
-- where PathSum.Adder.Tool's carryRippleᶜ writes the reversed netlist's
-- Toffoli gates with tof₃ itself.  As a check that this is the tool's
-- circuit, gate for gate: at n = 2 and n = 3, read as the tool writes
-- gates (prim: H, T, Tinv and CNOT on numbered wires), it is the list
-- the tool's own carryRipple produces on its variable list
-- a ++ b ++ c ++ anc ++ carry (Feynman-2, Feynman-3, by evaluation;
-- the lists were printed by running the tool's toffoli, carryRipple
-- and dagger, copied verbatim, under GHC -- 80 and 155 gates, and at
-- n = 8 and n = 16 the same run prints table 2's statistics).
--
-- It computes the netlist's Boolean function (feynmanᶜ-computes).
-- Compute and copy do so for their parts (PathSum.Adder.Tool.
-- expand₃-computes); the adjoint of a circuit computing a permutation
-- computes the inverse permutation (PathSum.Classical.Adjoint: the
-- path-sum of C† is the conjugate transpose of C's, by
-- PathSum.CRK.Conjugate, and a real permutation matrix is inverted by
-- its transpose), which for compute is the reversed netlist's
-- function, every gate of a netlist being an involution (†-run); and
-- by proposition 2.7 the three compose to the netlist's
-- compute ++ copy ++ reverse compute, which is carryRipple.  So its
-- path-sum is PathSum.Adder.Tool's, up to ≋ (feynmanᶜ-≋, Feynman-≋),
-- and PathSum.Adder.Tool's theorems hold for it: on the inputs whose
-- ancillas read 0 it is the tool's specification (feynmanᶜ-spec), the
-- ancillas are left clean (feynmanᶜ-clean), and with them read as the
-- constant 0 the path-sums are ≋ (feynmanᶜ-set0) -- the statement the
-- tool checked at n = 8 and n = 16 -- and on the tool's layout, for
-- every n ≥ 1, Feynman-spec, Feynman-clean and Feynman-set0.  The
-- Toffoli gate's adjoint circuit computes the Toffoli gate
-- (tof₃†-computes).
--
-- Its counts are carryRippleᶜ's: inverting keeps the Hadamards, so the
-- path variables, exchanges T and T†, so keeps the T count, and keeps
-- the Clifford gates (norm-†, tcount-†, cliffords-†); and it touches
-- as many wires, all 5n for n ≥ 2 (Feynman-qubits) and four for n = 1
-- (Feynman-qubits-1, Feynman-qubits-Tool).  So its rows are table 2's,
-- each counted from this circuit (Adder8-Feynman, Adder16-Feynman):
--
--                 qubits   path vars   Clifford     T
--    Adder8          40        56         334      196
--    Adder16         80       120         710      420
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Adder.Feynman (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; _∧_; _xor_)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; reverse; map)
open import Data.List.Properties using
  (++-assoc; ++-identityʳ; unfold-reverse)
open import Data.Nat.Base using (zero; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using ([_,_]′)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adder.CarryRipple using
  (Line; compute; copyᶠ; carryRipple; carryRipple-count;
   carryRipple-computes; carryRipple-toffolis; carryRipple-cnots;
   additionᶠ-work; standardᶠ)
open import PathSum.Adder.Layout using (Layout)
open import PathSum.Adder.Tool M₀ using
  (expand₃; expand₃-computes; norm-expand₃; tcount-expand₃;
   cliffords-expand₃; ∈ᶜ-expand₃; toolˢ; toolˢ-computes; fun-toolˢ;
   ancᶠ; cleanᶠ⇔blankᶠ; ancᶠ-work; carryRippleᶜ; carryRippleᶜ-computes;
   CarryRippleᶜ; Tool-qubits)
open import PathSum.Adder.Wires using (Tool-wires)
open import PathSum.Ancillas M₀ using
  (Clean; set0ˢ; _≋[_]₀*_; ≋[]₀*⇔set0ˢ; computes⇒≋[]₀*; clean-ancillas)
open import PathSum.Assign using (_[_≔_]; ≔-cong)
open import PathSum.Classical M₀ using
  (_computes_; computes-≗; computes-≋; outBit-none; ⟦++⟧-computes)
open import PathSum.Classical.Adjoint M₀ using (†-involution; †-run)
open import PathSum.CRK.Adjoint M using (inv; _†; †-++; norm-++; norm-†)
open import PathSum.CRK.Circuit M using (paths≡norm)
open import PathSum.CRK.Path M₀ using
  (Gate; H; CNOT; R; R†; Circuit; ⟦_⟧; norm; paths)
open import PathSum.CRK.Qubits M₀ using
  (∈ᶜ-++ˡ; ∈ᶜ-++ʳ; qubits; qubits-all)
open import PathSum.Cyclotomic M₀ using (_≐_; 0ᴬ)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.QFT.Count M₀ using (cliffords; cliffords-++)
open import PathSum.Reversible using
  (ccx; cx; run; run-++; recover; is-ccx; is-cx; toffolis; cnots)
  renaming (Gate to Gateᴿ)
open import PathSum.Toffoli.Depth3 M₀ using (tof₃; tof₃-computes)
open import PathSum.Toffoli.Gate M₀ using (toffoli; toffoli-involutive)
open import PathSum.Toffoli.Netlist M₀ using (tcount; tcount-++)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The tool's circuit

-- carryRipple = compute ++ copy ++ dagger compute, compute and copy
-- written out over Clifford+T.

feynmanᶜ : {m N : ℕ} → Layout (Line m) N → Circuit N
feynmanᶜ L = expand₃ (compute L) ++ expand₃ (copyᶠ L) ++ expand₃ (compute L) †

-- On the tool's layout, 5n wires: a, b, c, anc, carry (n = m + 1).

Feynmanᶜ : (m : ℕ) → Circuit (5 * suc m)
Feynmanᶜ m = feynmanᶜ (standardᶠ m)


------------------------------------------------------------------------
-- Gate for gate

-- The adjoint of the tool's Toffoli circuit: its sixteen gates last to
-- first, T and T† exchanged -- the tool's dagger (toffoli x y z).

tof₃† : (c₁ c₂ t : Fin n) → c₁ ≢ c₂ → c₁ ≢ t → c₂ ≢ t → Circuit n
tof₃† c₁ c₂ t p q r = tof₃ c₁ c₂ t p q r †

-- A netlist written out with it.

expand₃† : List (Gateᴿ n) → Circuit n
expand₃† []                       = []
expand₃† (ccx c₁ c₂ t p q r ∷ gs) =
  tof₃† c₁ c₂ t (recover p) (recover q) (recover r) ++ expand₃† gs
expand₃† (cx c t p ∷ gs)          = CNOT c t (recover p) ∷ expand₃† gs

expand₃†-++ : (gs hs : List (Gateᴿ n)) →
              expand₃† (gs ++ hs) ≡ expand₃† gs ++ expand₃† hs
expand₃†-++ []                       hs = refl
expand₃†-++ (ccx c₁ c₂ t p q r ∷ gs) hs =
  trans (cong (B ++_) (expand₃†-++ gs hs))
        (sym (++-assoc B (expand₃† gs) (expand₃† hs)))
  where
  B = tof₃† c₁ c₂ t (recover p) (recover q) (recover r)
expand₃†-++ (cx c t p ∷ gs)          hs =
  cong (CNOT c t (recover p) ∷_) (expand₃†-++ gs hs)

-- The adjoint of a netlist written out is the reversed netlist written
-- out with the adjoint Toffoli circuit.

†-expand₃ : (gs : List (Gateᴿ n)) → expand₃ gs † ≡ expand₃† (reverse gs)
†-expand₃ []       = refl
†-expand₃ (g ∷ gs) =
  trans (block g)
  (trans (cong (_++ expand₃† (g ∷ [])) (†-expand₃ gs))
  (trans (sym (expand₃†-++ (reverse gs) (g ∷ [])))
         (cong expand₃† (sym (unfold-reverse g gs)))))
  where
  block : (g : Gateᴿ _) → expand₃ (g ∷ gs) † ≡ expand₃ gs † ++ expand₃† (g ∷ [])
  block (ccx c₁ c₂ t p q r) =
    trans (†-++ T (expand₃ gs))
          (cong (expand₃ gs † ++_) (sym (++-identityʳ (T †))))
    where
    T = tof₃ c₁ c₂ t (recover p) (recover q) (recover r)
  block (cx c t p)          = refl

-- So the uncompute half is the netlist's compute reversed, each Toffoli
-- gate written out by the adjoint circuit.

feynmanᶜ-blocks : {m N : ℕ} (L : Layout (Line m) N) →
                  feynmanᶜ L ≡
                  expand₃ (compute L) ++ expand₃ (copyᶠ L) ++
                  expand₃† (reverse (compute L))
feynmanᶜ-blocks L =
  cong (λ D → expand₃ (compute L) ++ expand₃ (copyᶠ L) ++ D)
       (†-expand₃ (compute L))


------------------------------------------------------------------------
-- The tool's gate lists

-- A gate as the tool writes it (Feynman.Core's Primitive), its wires
-- numbered: H, T (R_3), Tinv (R_3†) and CNOT, and any other R_k or
-- R_k† (none occurs here).

data Primitive : Set where
  H′ T′ Tinv′ : ℕ → Primitive
  CNOT′ R′ R†′ : ℕ → ℕ → Primitive

prim : Gate n → Primitive
prim (H w)                         = H′ (toℕ w)
prim (CNOT c t _)                  = CNOT′ (toℕ c) (toℕ t)
prim (R (suc (suc (suc zero))) w)  = T′ (toℕ w)
prim (R k w)                       = R′ k (toℕ w)
prim (R† (suc (suc (suc zero))) w) = Tinv′ (toℕ w)
prim (R† k w)                      = R†′ k (toℕ w)

-- At n = 2 and n = 3 the circuit is the list the tool's carryRipple
-- produces, wires numbered by its variable list a ++ b ++ c ++ anc ++
-- carry (the tool's printVerStats reports 10 and 15 qubits, 8 and 16
-- path variables, 52 and 99 Clifford gates, 28 and 56 T gates).

Feynman-2 :
  map prim (Feynmanᶜ 1) ≡
  CNOT′ 0 6 ∷ CNOT′ 2 6 ∷ CNOT′ 2 8 ∷ H′ 9 ∷ T′ 0 ∷ T′ 8 ∷ T′ 9 ∷
  CNOT′ 0 8 ∷ CNOT′ 8 9 ∷ CNOT′ 9 0 ∷ Tinv′ 0 ∷ Tinv′ 8 ∷ T′ 9 ∷
  CNOT′ 8 0 ∷ Tinv′ 0 ∷ CNOT′ 8 9 ∷ CNOT′ 9 0 ∷ CNOT′ 0 8 ∷ H′ 9 ∷
  CNOT′ 2 8 ∷ H′ 9 ∷ T′ 2 ∷ T′ 8 ∷ T′ 9 ∷ CNOT′ 2 8 ∷ CNOT′ 8 9 ∷
  CNOT′ 9 2 ∷ Tinv′ 2 ∷ Tinv′ 8 ∷ T′ 9 ∷ CNOT′ 8 2 ∷ Tinv′ 2 ∷
  CNOT′ 8 9 ∷ CNOT′ 9 2 ∷ CNOT′ 2 8 ∷ H′ 9 ∷ CNOT′ 1 7 ∷ CNOT′ 3 7 ∷
  CNOT′ 9 7 ∷ CNOT′ 6 4 ∷ CNOT′ 7 5 ∷ CNOT′ 9 7 ∷ CNOT′ 3 7 ∷
  CNOT′ 1 7 ∷ H′ 9 ∷ CNOT′ 2 8 ∷ CNOT′ 9 2 ∷ CNOT′ 8 9 ∷ T′ 2 ∷
  CNOT′ 8 2 ∷ Tinv′ 9 ∷ T′ 8 ∷ T′ 2 ∷ CNOT′ 9 2 ∷ CNOT′ 8 9 ∷
  CNOT′ 2 8 ∷ Tinv′ 9 ∷ Tinv′ 8 ∷ Tinv′ 2 ∷ H′ 9 ∷ CNOT′ 2 8 ∷ H′ 9 ∷
  CNOT′ 0 8 ∷ CNOT′ 9 0 ∷ CNOT′ 8 9 ∷ T′ 0 ∷ CNOT′ 8 0 ∷ Tinv′ 9 ∷
  T′ 8 ∷ T′ 0 ∷ CNOT′ 9 0 ∷ CNOT′ 8 9 ∷ CNOT′ 0 8 ∷ Tinv′ 9 ∷ Tinv′ 8 ∷
  Tinv′ 0 ∷ H′ 9 ∷ CNOT′ 2 8 ∷ CNOT′ 2 6 ∷ CNOT′ 0 6 ∷ []
Feynman-2 = refl

Feynman-3 :
  map prim (Feynmanᶜ 2) ≡
  CNOT′ 0 9 ∷ CNOT′ 3 9 ∷ CNOT′ 3 12 ∷ H′ 13 ∷ T′ 0 ∷ T′ 12 ∷ T′ 13 ∷
  CNOT′ 0 12 ∷ CNOT′ 12 13 ∷ CNOT′ 13 0 ∷ Tinv′ 0 ∷ Tinv′ 12 ∷ T′ 13 ∷
  CNOT′ 12 0 ∷ Tinv′ 0 ∷ CNOT′ 12 13 ∷ CNOT′ 13 0 ∷ CNOT′ 0 12 ∷
  H′ 13 ∷ CNOT′ 3 12 ∷ H′ 13 ∷ T′ 3 ∷ T′ 12 ∷ T′ 13 ∷ CNOT′ 3 12 ∷
  CNOT′ 12 13 ∷ CNOT′ 13 3 ∷ Tinv′ 3 ∷ Tinv′ 12 ∷ T′ 13 ∷ CNOT′ 12 3 ∷
  Tinv′ 3 ∷ CNOT′ 12 13 ∷ CNOT′ 13 3 ∷ CNOT′ 3 12 ∷ H′ 13 ∷
  CNOT′ 1 10 ∷ CNOT′ 4 10 ∷ CNOT′ 13 10 ∷ CNOT′ 4 13 ∷ H′ 14 ∷ T′ 1 ∷
  T′ 13 ∷ T′ 14 ∷ CNOT′ 1 13 ∷ CNOT′ 13 14 ∷ CNOT′ 14 1 ∷ Tinv′ 1 ∷
  Tinv′ 13 ∷ T′ 14 ∷ CNOT′ 13 1 ∷ Tinv′ 1 ∷ CNOT′ 13 14 ∷ CNOT′ 14 1 ∷
  CNOT′ 1 13 ∷ H′ 14 ∷ CNOT′ 4 13 ∷ H′ 14 ∷ T′ 4 ∷ T′ 13 ∷ T′ 14 ∷
  CNOT′ 4 13 ∷ CNOT′ 13 14 ∷ CNOT′ 14 4 ∷ Tinv′ 4 ∷ Tinv′ 13 ∷ T′ 14 ∷
  CNOT′ 13 4 ∷ Tinv′ 4 ∷ CNOT′ 13 14 ∷ CNOT′ 14 4 ∷ CNOT′ 4 13 ∷
  H′ 14 ∷ CNOT′ 2 11 ∷ CNOT′ 5 11 ∷ CNOT′ 14 11 ∷ CNOT′ 9 6 ∷
  CNOT′ 10 7 ∷ CNOT′ 11 8 ∷ CNOT′ 14 11 ∷ CNOT′ 5 11 ∷ CNOT′ 2 11 ∷
  H′ 14 ∷ CNOT′ 4 13 ∷ CNOT′ 14 4 ∷ CNOT′ 13 14 ∷ T′ 4 ∷ CNOT′ 13 4 ∷
  Tinv′ 14 ∷ T′ 13 ∷ T′ 4 ∷ CNOT′ 14 4 ∷ CNOT′ 13 14 ∷ CNOT′ 4 13 ∷
  Tinv′ 14 ∷ Tinv′ 13 ∷ Tinv′ 4 ∷ H′ 14 ∷ CNOT′ 4 13 ∷ H′ 14 ∷
  CNOT′ 1 13 ∷ CNOT′ 14 1 ∷ CNOT′ 13 14 ∷ T′ 1 ∷ CNOT′ 13 1 ∷
  Tinv′ 14 ∷ T′ 13 ∷ T′ 1 ∷ CNOT′ 14 1 ∷ CNOT′ 13 14 ∷ CNOT′ 1 13 ∷
  Tinv′ 14 ∷ Tinv′ 13 ∷ Tinv′ 1 ∷ H′ 14 ∷ CNOT′ 4 13 ∷ CNOT′ 13 10 ∷
  CNOT′ 4 10 ∷ CNOT′ 1 10 ∷ H′ 13 ∷ CNOT′ 3 12 ∷ CNOT′ 13 3 ∷
  CNOT′ 12 13 ∷ T′ 3 ∷ CNOT′ 12 3 ∷ Tinv′ 13 ∷ T′ 12 ∷ T′ 3 ∷
  CNOT′ 13 3 ∷ CNOT′ 12 13 ∷ CNOT′ 3 12 ∷ Tinv′ 13 ∷ Tinv′ 12 ∷
  Tinv′ 3 ∷ H′ 13 ∷ CNOT′ 3 12 ∷ H′ 13 ∷ CNOT′ 0 12 ∷ CNOT′ 13 0 ∷
  CNOT′ 12 13 ∷ T′ 0 ∷ CNOT′ 12 0 ∷ Tinv′ 13 ∷ T′ 12 ∷ T′ 0 ∷
  CNOT′ 13 0 ∷ CNOT′ 12 13 ∷ CNOT′ 0 12 ∷ Tinv′ 13 ∷ Tinv′ 12 ∷
  Tinv′ 0 ∷ H′ 13 ∷ CNOT′ 3 12 ∷ CNOT′ 3 9 ∷ CNOT′ 0 9 ∷ []
Feynman-3 = refl


------------------------------------------------------------------------
-- What it computes

-- The adjoint Toffoli circuit computes the Toffoli gate: the Toffoli
-- function is an involution.

private
  toffoli-cong : (c₁ c₂ t : Fin n) {x x′ : Assign n} →
                 (∀ w → x w ≡ x′ w) →
                 ∀ w → toffoli c₁ c₂ t x w ≡ toffoli c₁ c₂ t x′ w
  toffoli-cong c₁ c₂ t {x} {x′} h w =
    trans (cong (λ b → (x [ t ≔ b ]) w)
                (cong₂ _xor_ (h t) (cong₂ _∧_ (h c₁) (h c₂))))
          (≔-cong t (x′ t xor (x′ c₁ ∧ x′ c₂)) h w)

tof₃†-computes : (c₁ c₂ t : Fin n) (p : c₁ ≢ c₂) (q : c₁ ≢ t)
                 (r : c₂ ≢ t) →
                 ⟦ tof₃† c₁ c₂ t p q r ⟧ computes toffoli c₁ c₂ t
tof₃†-computes c₁ c₂ t p q r =
  †-involution (tof₃ c₁ c₂ t p q r) (toffoli-cong c₁ c₂ t)
               (toffoli-involutive c₁ c₂ t q r) (tof₃-computes c₁ c₂ t p q r)

-- The whole circuit computes the netlist's function: compute, copy,
-- and the adjoint of compute computing the reversed compute.

feynmanᶜ-computes : {m N : ℕ} (L : Layout (Line m) N) →
                    ⟦ feynmanᶜ L ⟧ computes run (carryRipple L)
feynmanᶜ-computes {m} {N} L =
  computes-≗ ⟦ feynmanᶜ L ⟧ (λ x w → sym (run-carryRipple x w))
    (⟦++⟧-computes A (B ++ A †) (expand₃-computes (compute L))
      (⟦++⟧-computes B (A †) (expand₃-computes (copyᶠ L))
        (†-run A (compute L) (expand₃-computes (compute L)))))
  where
  A B : Circuit N
  A = expand₃ (compute L)
  B = expand₃ (copyᶠ L)

  run-carryRipple : ∀ x w →
                    run (carryRipple L) x w ≡
                    run (reverse (compute L))
                        (run (copyᶠ L) (run (compute L) x)) w
  run-carryRipple x w =
    trans (cong (λ f → f w)
                (run-++ (compute L) (copyᶠ L ++ reverse (compute L)) x))
          (cong (λ f → f w)
                (run-++ (copyᶠ L) (reverse (compute L)) (run (compute L) x)))

-- So it is PathSum.Adder.Tool's circuit, up to ≋, on every input.

feynmanᶜ-≋ : {m N : ℕ} (L : Layout (Line m) N) →
             ⟦ feynmanᶜ L ⟧ ≋ ⟦ carryRippleᶜ L ⟧
feynmanᶜ-≋ L =
  computes-≋ ⟦ feynmanᶜ L ⟧ ⟦ carryRippleᶜ L ⟧
             (feynmanᶜ-computes L) (carryRippleᶜ-computes L)

-- On the inputs whose ancillas read 0 it is the tool's specification.

feynmanᶜ-spec : {m N : ℕ} (L : Layout (Line m) N) →
                ⟦ feynmanᶜ L ⟧ ≋[ ancᶠ L ]₀* toolˢ L
feynmanᶜ-spec L =
  computes⇒≋[]₀* ⟦ feynmanᶜ L ⟧ (toolˢ L) (ancᶠ L)
    (feynmanᶜ-computes L) (toolˢ-computes L)
    (λ x cl w →
       carryRipple-computes L x (Equivalence.to (cleanᶠ⇔blankᶠ L x) cl) w)

-- The ancillas are left clean.

feynmanᶜ-clean : {m N : ℕ} (L : Layout (Line m) N) → ∀ x z →
                 Clean (ancᶠ L) x → (j : Fin (suc m + suc m)) →
                 z (ancᶠ L j) ≡ true → amp ⟦ feynmanᶜ L ⟧ x z ≐ 0ᴬ
feynmanᶜ-clean L = clean-ancillas (ancᶠ L) (feynmanᶜ-spec L) out0
  where
  out0 : ∀ x (y : Assign 0) → Clean (ancᶠ L) x →
         ∀ j → outBit (toolˢ L) x y (ancᶠ L j) ≡ false
  out0 x y cl j =
    trans (outBit-none (toolˢ L) x y (ancᶠ L j))
    (trans (fun-toolˢ L x (ancᶠ L j))
    (trans (additionᶠ-work L x (ancᶠ L j) (ancᶠ-work L j)) (cl j)))

-- With the ancillas read as the constant 0 on both sides, as the tool
-- reads them, the path-sums are equivalent.

feynmanᶜ-set0 : {m N : ℕ} (L : Layout (Line m) N) →
                set0ˢ (ancᶠ L) ⟦ feynmanᶜ L ⟧ ≋ set0ˢ (ancᶠ L) (toolˢ L)
feynmanᶜ-set0 L =
  Equivalence.to (≋[]₀*⇔set0ˢ (ancᶠ L) ⟦ feynmanᶜ L ⟧ (toolˢ L))
                 (feynmanᶜ-spec L)

-- On the tool's layout, for every n ≥ 1.

Feynman-≋ : (m : ℕ) → ⟦ Feynmanᶜ m ⟧ ≋ ⟦ CarryRippleᶜ m ⟧
Feynman-≋ m = feynmanᶜ-≋ (standardᶠ m)

Feynman-spec : (m : ℕ) → ⟦ Feynmanᶜ m ⟧ ≋[ ancᶠ (standardᶠ m) ]₀*
                           toolˢ (standardᶠ m)
Feynman-spec m = feynmanᶜ-spec (standardᶠ m)

Feynman-clean : (m : ℕ) → ∀ x z → Clean (ancᶠ (standardᶠ m)) x →
                (j : Fin (suc m + suc m)) →
                z (ancᶠ (standardᶠ m) j) ≡ true →
                amp ⟦ Feynmanᶜ m ⟧ x z ≐ 0ᴬ
Feynman-clean m = feynmanᶜ-clean (standardᶠ m)

Feynman-set0 : (m : ℕ) →
               set0ˢ (ancᶠ (standardᶠ m)) ⟦ Feynmanᶜ m ⟧ ≋
               set0ˢ (ancᶠ (standardᶠ m)) (toolˢ (standardᶠ m))
Feynman-set0 m = feynmanᶜ-set0 (standardᶠ m)


------------------------------------------------------------------------
-- Resources

-- Inverting a circuit keeps its T gates (T and T† exchanged) and its
-- Clifford gates; it keeps its Hadamards (PathSum.CRK.Adjoint.norm-†).

private
  tcount-inv : (g : Gate n) → tcount (inv g ∷ []) ≡ tcount (g ∷ [])
  tcount-inv (H _)                           = refl
  tcount-inv (CNOT _ _ _)                    = refl
  tcount-inv (R zero _)                      = refl
  tcount-inv (R (suc zero) _)                = refl
  tcount-inv (R (suc (suc zero)) _)          = refl
  tcount-inv (R (suc (suc (suc zero))) _)    = refl
  tcount-inv (R (suc (suc (suc (suc _)))) _) = refl
  tcount-inv (R† zero _)                      = refl
  tcount-inv (R† (suc zero) _)                = refl
  tcount-inv (R† (suc (suc zero)) _)          = refl
  tcount-inv (R† (suc (suc (suc zero))) _)    = refl
  tcount-inv (R† (suc (suc (suc (suc _)))) _) = refl

  cliffords-inv : (g : Gate n) → cliffords (inv g ∷ []) ≡ cliffords (g ∷ [])
  cliffords-inv (H _)        = refl
  cliffords-inv (CNOT _ _ _) = refl
  cliffords-inv (R _ _)      = refl
  cliffords-inv (R† _ _)     = refl

tcount-† : (C : Circuit n) → tcount (C †) ≡ tcount C
tcount-† []      = refl
tcount-† (g ∷ C) =
  trans (tcount-++ (C †) (inv g ∷ []))
  (trans (cong₂ _+_ (tcount-† C) (tcount-inv g))
  (trans (+-comm (tcount C) (tcount (g ∷ [])))
         (sym (tcount-++ (g ∷ []) C))))

cliffords-† : (C : Circuit n) → cliffords (C †) ≡ cliffords C
cliffords-† []      = refl
cliffords-† (g ∷ C) =
  trans (cliffords-++ (C †) (inv g ∷ []))
  (trans (cong₂ _+_ (cliffords-† C) (cliffords-inv g))
  (trans (+-comm (cliffords C) (cliffords (g ∷ [])))
         (sym (cliffords-++ (g ∷ []) C))))

-- So the circuit has carryRippleᶜ's counts: per Toffoli gate of the
-- netlist two path variables, seven T gates and nine Clifford gates,
-- per CNOT one Clifford gate.

module _ {m N : ℕ} (L : Layout (Line m) N) where

  private
    A B : Circuit N
    A = expand₃ (compute L)
    B = expand₃ (copyᶠ L)

    t c t′ c′ : ℕ
    t  = toffolis (compute L)
    c  = cnots (compute L)
    t′ = toffolis (copyᶠ L)
    c′ = cnots (copyᶠ L)

  feynmanᶜ-norm : norm (feynmanᶜ L) ≡ toffolis (carryRipple L) * 2
  feynmanᶜ-norm =
    trans (norm-++ A (B ++ A †))
    (trans (cong (norm A +_)
                 (trans (norm-++ B (A †)) (cong (norm B +_) (norm-† A))))
    (trans (cong₂ (λ a b → a + (b + a))
                  (norm-expand₃ (compute L)) (norm-expand₃ (copyᶠ L)))
    (trans (solve 2 (λ t t′ → t :* con 2 :+ (t′ :* con 2 :+ t :* con 2)
                              := (t :+ (t′ :+ t)) :* con 2) refl t t′)
           (cong (_* 2) (sym (carryRipple-count is-ccx L))))))

  feynmanᶜ-tcount : tcount (feynmanᶜ L) ≡ toffolis (carryRipple L) * 7
  feynmanᶜ-tcount =
    trans (tcount-++ A (B ++ A †))
    (trans (cong (tcount A +_)
                 (trans (tcount-++ B (A †))
                        (cong (tcount B +_) (tcount-† A))))
    (trans (cong₂ (λ a b → a + (b + a))
                  (tcount-expand₃ (compute L)) (tcount-expand₃ (copyᶠ L)))
    (trans (solve 2 (λ t t′ → t :* con 7 :+ (t′ :* con 7 :+ t :* con 7)
                              := (t :+ (t′ :+ t)) :* con 7) refl t t′)
           (cong (_* 7) (sym (carryRipple-count is-ccx L))))))

  feynmanᶜ-cliffords : cliffords (feynmanᶜ L) ≡
                       toffolis (carryRipple L) * 9 + cnots (carryRipple L)
  feynmanᶜ-cliffords =
    trans (cliffords-++ A (B ++ A †))
    (trans (cong (cliffords A +_)
                 (trans (cliffords-++ B (A †))
                        (cong (cliffords B +_) (cliffords-† A))))
    (trans (cong₂ (λ a b → a + (b + a))
                  (cliffords-expand₃ (compute L))
                  (cliffords-expand₃ (copyᶠ L)))
    (trans (solve 4 (λ t c t′ c′ →
                       (t :* con 9 :+ c) :+
                       ((t′ :* con 9 :+ c′) :+ (t :* con 9 :+ c))
                       := (t :+ (t′ :+ t)) :* con 9 :+ (c :+ (c′ :+ c)))
                    refl t c t′ c′)
           (cong₂ (λ a b → a * 9 + b)
                  (sym (carryRipple-count is-ccx L))
                  (sym (carryRipple-count is-cx L))))))

-- For every n ≥ 1: 8(n − 1) path variables, 28(n − 1) T gates and
-- 36(n − 1) + 11n − 6 Clifford gates, as for carryRippleᶜ.

Feynman-paths : (m : ℕ) → paths (Feynmanᶜ m) ≡ 4 * m * 2
Feynman-paths m =
  trans (paths≡norm (Feynmanᶜ m))
  (trans (feynmanᶜ-norm (standardᶠ m))
         (cong (_* 2) (carryRipple-toffolis (standardᶠ m))))

Feynman-tcount : (m : ℕ) → tcount (Feynmanᶜ m) ≡ 4 * m * 7
Feynman-tcount m =
  trans (feynmanᶜ-tcount (standardᶠ m))
        (cong (_* 7) (carryRipple-toffolis (standardᶠ m)))

Feynman-cliffords : (m : ℕ) → cliffords (Feynmanᶜ m) ≡
                    4 * m * 9 + (11 * suc m ∸ 6)
Feynman-cliffords m =
  trans (feynmanᶜ-cliffords (standardᶠ m))
        (cong₂ (λ t c → t * 9 + c) (carryRipple-toffolis (standardᶠ m))
                                   (carryRipple-cnots (standardᶠ m)))

-- Its qubits, as the tool counts them: all 5n wires for n ≥ 2, the
-- compute or the copy touching each (PathSum.Adder.Wires.Tool-wires);
-- four for n = 1, as the tool's own count has it.

Feynman-qubits : (m : ℕ) → m ≢ 0 → qubits (Feynmanᶜ m) ≡ 5 * suc m
Feynman-qubits m p =
  qubits-all (Feynmanᶜ m) λ u →
    [ (λ q → ∈ᶜ-++ˡ A (B ++ A †) (∈ᶜ-expand₃ (compute L) q))
    , (λ q → ∈ᶜ-++ʳ A (B ++ A †)
               (∈ᶜ-++ˡ B (A †) (∈ᶜ-expand₃ (copyᶠ L) q)))
    ]′ (Tool-wires m p u)
  where
  L = standardᶠ m
  A = expand₃ (compute L)
  B = expand₃ (copyᶠ L)

Feynman-qubits-1 : qubits (Feynmanᶜ 0) ≡ 4
Feynman-qubits-1 = refl

-- So, for every n, as many as carryRippleᶜ.

Feynman-qubits-Tool : (m : ℕ) → qubits (Feynmanᶜ m) ≡ qubits (CarryRippleᶜ m)
Feynman-qubits-Tool zero    = refl
Feynman-qubits-Tool (suc m) =
  trans (Feynman-qubits (suc m) (λ ())) (sym (Tool-qubits (suc m) (λ ())))

-- Table 2's Adder8 and Adder16, each counted from this circuit.

Adder8-Feynman :
  (qubits (Feynmanᶜ 7) ≡ 40) × (paths (Feynmanᶜ 7) ≡ 56) ×
  (cliffords (Feynmanᶜ 7) ≡ 334) × (tcount (Feynmanᶜ 7) ≡ 196)
Adder8-Feynman =
  Feynman-qubits 7 (λ ()) , Feynman-paths 7 , Feynman-cliffords 7 ,
  Feynman-tcount 7

Adder16-Feynman :
  (qubits (Feynmanᶜ 15) ≡ 80) × (paths (Feynmanᶜ 15) ≡ 120) ×
  (cliffords (Feynmanᶜ 15) ≡ 710) × (tcount (Feynmanᶜ 15) ≡ 420)
Adder16-Feynman =
  Feynman-qubits 15 (λ ()) , Feynman-paths 15 , Feynman-cliffords 15 ,
  Feynman-tcount 15
