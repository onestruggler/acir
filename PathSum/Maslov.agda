------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-bit Toffoli gate by the Maslov decomposition: relative-phase
-- Toffoli gates and ⌈(n − 3)/2⌉ ancillas, for every n (Amy, QPL 2018,
-- section 5.2 and table 2)
--
-- Section 5.2 verifies two Clifford+T implementations of
--
--    Toffoli_n : |x₁ x₂ … x_n⟩ ↦ |x₁ x₂ … (x_n ⊕ x₁ x₂ ⋯ x_(n−1))⟩,
--
-- "the standard decomposition into 2(n − 3) + 1 Toffoli gates and
-- n − 3 ancillas" (PathSum.ToffoliN) and "the Maslov decomposition
-- [23] using relative phase Toffolis and ⌈(n − 3)/2⌉ ancillas", each
-- up to n = 100 by computation.  This module proves the second for
-- every n at once.
--
-- The plan.  The construction is the one the paper's tool generates,
-- maslovToffoli in Feynman's src/Feynman/Verification/SOP.hs: its
-- rToffoli4 (rc3x below) from three controls into a fresh ancilla,
-- recursively on that ancilla and the remaining controls, then the
-- gate's adjoint; with two wires left a CNOT, with three the tool's
-- own sixteen-gate Toffoli circuit (its toffoli: PathSum.Toffoli.
-- Depth3's tof₃).  It is the tool's circuit gate for gate, at every n
-- (PathSum.Maslov.Feynman.Maslovₙ-tool: read as the tool writes gates,
-- it is the list maslovToffoli produces on the inputs 0 … n − 1, the
-- ancillas _anc0, _anc1, … being the wires n, n + 1, …).  Table 2's
-- counts are exactly this construction's (PathSum.RelativePhase's
-- header has the analysis).  It is a variant of Maslov's own, [23]'s
-- Proposition 4, which keeps an exact Toffoli gate in the middle at
-- every n: 8n − 17 T gates, one fewer than table 2's 8n − 16 at even
-- n.  At odd n the two have the same structure and the same T and
-- Hadamard counts, but the tool's Toffoli circuit has seven CNOTs
-- where [23]'s has six: 6n − 11 CNOTs here (the Clifford gates below
-- less the Hadamards), 6n − 12 in [23].
--
-- * The gates (phase A): PathSum.Maslov.Gate4's relative-phase
--   Toffoli-4 gate rc3x a b c d, three controls and a target, eight T
--   gates, four Hadamards and six CNOTs, which computes the three-
--   control Toffoli function only up to the relative phase
--   ¼ x_a x_b + ¼ x_a x_b x_c + ½ x_a x_b x_d (rc3x-up-to; it is not
--   the Toffoli-4 gate, rc3x-not-toffoli), and its inverse rc3x †,
--   which computes it up to minus the phase read after it; around any
--   circuit that leaves a, b, c and d alone the two phases cancel
--   (rc3x-sandwich).
--
-- * The construction (PathSum.Maslov.Chain): on m + 1 controls, a
--   target and ⌊m/2⌋ ancillas (n = m + 2, ⌊m/2⌋ = ⌈(n − 3)/2⌉), a
--   chain of relative-phase Toffoli-4 gates computes the conjunction
--   of the controls into the ancillas -- a₀ ⊕= c₀ c₁ c₂, then
--   a₁ ⊕= a₀ c₃ c₄, and so on, two more controls per ancilla -- a
--   middle gate copies the conjunction onto the target, and the
--   mirrored chain of inverses uncomputes the ancillas.  For even n
--   the chain absorbs every control and the middle gate is a CNOT from
--   the last ancilla (from c₀ when n = 2); for odd n one control is
--   left over and the middle gate is a Toffoli gate, the tool's exact
--   sixteen-gate circuit tof₃ (seven T gates, like PathSum.Toffoli's
--   tof, and seven CNOTs where tof has six), on the last ancilla and
--   that control (on c₀ and c₁ when n = 3).  As a recursion (maslov):
--
--      maslov L = CNOT(c₀, t)                               m = 0
--               = tof₃(c₀, c₁, t)                           m = 1
--               = rc3x(c₀,c₁,c₂,a₀) ; maslov (inner L) ;
--                 rc3x(c₀,c₁,c₂,a₀) †                       m + 2,
--
--   inner L having controls a₀, c₃, c₄, … and ancillas a₁, a₂, ….
--
-- * The phases (maslov-computes).  The circuit is a nest of
--   sandwiches, and each is closed by the inverse of the gate that
--   opened it, whose wires the inside leaves alone
--   (PathSum.Maslov.Chain.inner-c₀ … inner-a₀).  So by rc3x-sandwich,
--   by induction on m, the relative phases cancel level by level and
--   the whole circuit computes the permutation applyᴹ L exactly --
--   phase 0 -- on every input, clean or not: its unnormalised
--   amplitude from x to z is √2^k δ(applyᴹ L x, z), k its number of
--   Hadamards (PathSum.Classical's _computes_, which is
--   PathSum.RelativePhase's _computes_up-to_ at the phase 0).  Only
--   the records are used: no statement about the amplitudes of a
--   concrete rc3x is restated here.  The middle gate is the one gate
--   whose phase nothing would cancel, which is why it must be exact:
--   PathSum.Classical's CNOT, or the tool's Toffoli circuit
--   (PathSum.Toffoli.Depth3.tof₃-computes), never a relative-phase
--   gate.  And the phases are real: each gate is closed by its
--   inverse, not by itself as a Toffoli gate would be, since the gate
--   followed by itself is not the identity
--   (PathSum.Maslov.Gate4.rc3x-rc3x-not-id).
--
-- * The theorem.  An ancilla enters in |0⟩, so the claim concerns the
--   columns at the inputs whose ancillas read 0 (clean inputs), where
--   applyᴹ L is Toffoli_n (PathSum.Maslov.Chain.applyᴹ-correct): the
--   circuit is Toffoli_n there,
--
--      ⟦ maslov L ⟧ ≋[ anc L ]₀* toffoliᴹˢ L                (maslov-spec)
--
--   (PathSum.Ancillas; toffoliᴹˢ L is the classical path-sum flipping
--   the target by the lift of x_c₀ ⋯ x_cm, the specification of
--   PathSum.ToffoliN's standard decomposition read off the controls
--   and target), and leaves the ancillas clean: from a clean input no
--   amplitude reaches an output with an ancilla at 1 (maslov-clean).
--   Equivalently, with the ancillas read as the constant 0 in the
--   polynomials of both sides -- the paper's treatment of an ancilla
--   prepared in |0⟩ -- the two path-sums are ≋ outright (maslov-set0).
--   Maslovₙ n is the construction on the paper's layout for every
--   n ≥ 3: n + ⌈(n − 3)/2⌉ wires, the controls wires 0 … n − 2, the
--   target wire n − 1, the ancillas the wires from n on
--   (PathSum.Maslov.Chain.standardᴹ); Maslovₙ-computes, Maslovₙ-spec,
--   Maslovₙ-clean and Maslovₙ-set0 are the theorems for it.
--
-- * Resources, against table 2.  With j = ⌊m/2⌋ = ⌈(n − 3)/2⌉
--   ancillas, the circuit has 2j relative-phase Toffoli-4 gates, each
--   with four Hadamards, eight T or T† gates and ten Clifford gates (H
--   and CNOT), and the middle gate: a CNOT for even n (no Hadamard, no
--   T, one Clifford gate), the tool's Toffoli circuit for odd n (two
--   Hadamards, seven T, nine Clifford: two H and seven CNOTs).  So,
--   with p = n mod 2, it has 8j + 2p path variables, one per Hadamard
--   (maslov-paths), 16j + 7p T gates (maslov-tcount) and 20j + 8p + 1
--   Clifford gates (maslov-cliffords; PathSum.QFT.Count's count of H,
--   CNOT and R_k, R_k† for k ≤ 2, of which the circuit has none).  In
--   closed form (the -closed lemmas): for even n, 4(n − 2) path
--   variables, 8(n − 2) = 8n − 16 T gates and 10(n − 2) + 1 Clifford
--   gates; for odd n, which the table does not use, 2, 1 and 2 fewer,
--   so 8n − 17 T gates and 10n − 21 Clifford gates (the tool's own
--   count at n = 51: 194 path variables, 489 Clifford and 391 T).
--
-- * Qubits, as the tool counts them: the wires some gate touches
--   (PathSum.CRK.Qubits.qubits).  The circuit touches every control,
--   the target and every ancilla of its layout (maslov-ctl, maslov-tgt,
--   maslov-anc: the first Toffoli-4 gate touches c₀, c₁, c₂ and a₀,
--   the inner construction the rest, the middle gate what is left;
--   PathSum.Maslov.Wires.∈ᶜ-rc3x, PathSum.Adder.Tool.∈ᶜ-tof₃), and on
--   the paper's layout these are all the wires
--   (PathSum.Maslov.Wires.standardᴹ-wires).  So no wire is idle
--   (Maslovₙ-touched), and for every n ≥ 3 the qubits are all
--   n + ⌈(n − 3)/2⌉ wires (Maslovₙ-qubits).  At n = 50 and n = 100:
--   74 and 149 qubits, 192 and 392 path variables, 481 and 981
--   Clifford gates, 384 and 784 T gates -- exactly table 2's rows
--   Maslov50 and Maslov100 (table-2-Maslov50, table-2-Maslov100), the
--   qubits counted from the circuit as the tool counts them, not read
--   off its type (its width, which is the same number).
--
-- * Checks.  The circuits for n = 4, 5 and 6 are displayed
--   (Maslov-4, Maslov-5, Maslov-6), as a check that the recursion
--   builds the chain described above on the paper's wires; and
--   PathSum.Maslov.Feynman proves the circuit is the tool's gate for
--   gate at every n, with the tool's lists for n = 3 … 7, as printed
--   by its own functions run under GHC.
--
-- Not formalised: the verifier's own run on these circuits.  The proof
-- composes where the paper's tool reduces: no path-sum of the whole
-- circuit is ever computed and no closed instance is evaluated, so the
-- statement costs the same for every n.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Maslov (M₀ : ℕ) where

open import Data.Bool.Base using (true; false)
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using
  (zero; _+_; _*_; _∸_; _≤_; z≤n; s≤s; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adder.Tool M₀ using (∈ᶜ-tof₃)
open import PathSum.Ancillas M₀ using
  (Clean; set0ˢ; _≋[_]₀*_; ≋[]₀*⇔set0ˢ; computes⇒≋[]₀*; clean-ancillas)
open import PathSum.Classical M₀ using
  (_computes_; classical-computes; computes-≗; ⟦CNOT⟧-computes;
   setWire; outBit-none)
open import PathSum.Compose.CRK M₀ using (norm-++)
open import PathSum.CRK.Adjoint M using (_†)
open import PathSum.CRK.Circuit M using (paths≡norm)
open import PathSum.CRK.Path M₀ using (CNOT; Circuit; ⟦_⟧; norm; paths)
open import PathSum.CRK.Qubits M₀ using
  (_∈ᶜ_; ∈ᶜ-++ˡ; ∈ᶜ-++ʳ; qubits; qubits-all)
open import PathSum.Cyclotomic M₀ using (_≐_; 0ᴬ)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Maslov.Chain M₀ using
  (Layout; ctl; tgt; anc; ctl≢tgt; c₀≢c₁; c₀; c₁; c₂; a₀; c₀≢a₀; c₁≢a₀;
   c₂≢a₀; inner; applyᴹ; inner-c₀; inner-c₁; inner-c₂; inner-a₀;
   toffoliᴹ; toffoliᴹᵉ; toffoliᴹˢ; fun-toffoliᴹˢ; toffoliᴹ-anc;
   applyᴹ-correct; layout; standardᴹ)
open import PathSum.Maslov.Gate4 M₀ using (rc3x; rc3x-sandwich)
open import PathSum.Maslov.Wires M₀ using (∈ᶜ-rc3x; standardᴹ-wires)
open import PathSum.Polynomial.Boolean using (liftᵉ)
open import PathSum.QFT.Count M₀ using (cliffords; cliffords-++)
open import PathSum.RelativePhase M₀ using
  (computes⇒up-to; up-to⇒computes; ≡ᴺ-refl)
open import PathSum.Toffoli.Depth3 M₀ using (tof₃; tof₃-computes)
open import PathSum.Toffoli.Netlist M₀ using (tcount; tcount-++)

private
  variable
    N m : ℕ


------------------------------------------------------------------------
-- The circuit on any layout

-- A CNOT with one control, the tool's sixteen-gate Toffoli circuit
-- with two, and with more the relative-phase Toffoli-4 gate
-- a₀ ⊕= c₀ c₁ c₂ and its inverse around the construction on the inner
-- layout.

maslov : Layout N m → Circuit N
maslov {m = zero}        L = CNOT (ctl L zero) (tgt L) (ctl≢tgt L zero) ∷ []
maslov {m = suc zero}    L =
  tof₃ (ctl L zero) (ctl L (suc zero)) (tgt L) (c₀≢c₁ L)
       (ctl≢tgt L zero) (ctl≢tgt L (suc zero))
maslov {m = suc (suc m)} L =
  rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L) (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L)
  ++ maslov (inner L)
  ++ rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L) (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L) †

-- On every input it computes the permutation applyᴹ L exactly: the
-- relative phase of each Toffoli-4 gate is cancelled by its inverse's
-- (PathSum.Maslov.Gate4.rc3x-sandwich), since the construction between
-- them leaves their four wires alone, and the middle gate is exact.

maslov-computes : (L : Layout N m) → ⟦ maslov L ⟧ computes applyᴹ L
maslov-computes {m = zero}        L =
  ⟦CNOT⟧-computes (ctl L zero) (tgt L) (ctl≢tgt L zero)
maslov-computes {m = suc zero}    L =
  tof₃-computes (ctl L zero) (ctl L (suc zero)) (tgt L) (c₀≢c₁ L)
                (ctl≢tgt L zero) (ctl≢tgt L (suc zero))
maslov-computes {m = suc (suc m)} L =
  up-to⇒computes _
    (rc3x-sandwich (c₀ L) (c₁ L) (c₂ L) (a₀ L)
                   (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L) (maslov (inner L))
                   (computes⇒up-to _ (maslov-computes (inner L)))
                   (inner-c₀ L) (inner-c₁ L) (inner-c₂ L) (inner-a₀ L))
    (λ _ → ≡ᴺ-refl)

-- The specification computes Toffoli_n; the two agree on clean
-- inputs.

toffoliᴹˢ-computes : (L : Layout N m) → toffoliᴹˢ L computes toffoliᴹ L
toffoliᴹˢ-computes L =
  computes-≗ (toffoliᴹˢ L) (fun-toffoliᴹˢ L)
    (classical-computes (setWire (tgt L) (liftᵉ (toffoliᴹᵉ L))))

maslov-spec : (L : Layout N m) → ⟦ maslov L ⟧ ≋[ anc L ]₀* toffoliᴹˢ L
maslov-spec L =
  computes⇒≋[]₀* ⟦ maslov L ⟧ (toffoliᴹˢ L) (anc L)
    (maslov-computes L) (toffoliᴹˢ-computes L) (applyᴹ-correct L)

-- The ancillas are left clean: from a clean input, no amplitude
-- reaches an output with an ancilla at 1.

maslov-clean : (L : Layout N m) → ∀ x z → Clean (anc L) x →
               (i : Fin ⌊ m /2⌋) → z (anc L i) ≡ true →
               amp ⟦ maslov L ⟧ x z ≐ 0ᴬ
maslov-clean L = clean-ancillas (anc L) (maslov-spec L) out0
  where
  out0 : ∀ x (y : Assign 0) → Clean (anc L) x →
         ∀ i → outBit (toffoliᴹˢ L) x y (anc L i) ≡ false
  out0 x y cl i = trans (outBit-none (toffoliᴹˢ L) x y (anc L i))
    (trans (fun-toffoliᴹˢ L x (anc L i)) (toffoliᴹ-anc L x cl i))

-- With the ancillas read as the constant 0 on both sides, the
-- circuit's path-sum is equivalent to the specification's.

maslov-set0 : (L : Layout N m) →
              set0ˢ (anc L) ⟦ maslov L ⟧ ≋ set0ˢ (anc L) (toffoliᴹˢ L)
maslov-set0 L =
  Equivalence.to (≋[]₀*⇔set0ˢ (anc L) ⟦ maslov L ⟧ (toffoliᴹˢ L))
                 (maslov-spec L)


------------------------------------------------------------------------
-- The paper's circuit, for every n ≥ 3

-- On n + ⌈(n − 3)/2⌉ wires: controls 0 … n − 2, target n − 1,
-- ancillas from n on (PathSum.Maslov.Chain.standardᴹ).

Maslovₙ : (n : ℕ) → 3 ≤ n → Circuit (n + ⌈ n ∸ 3 /2⌉)
Maslovₙ n p = maslov (standardᴹ n p)

Maslovₙ-computes : (n : ℕ) (p : 3 ≤ n) →
                   ⟦ Maslovₙ n p ⟧ computes applyᴹ (standardᴹ n p)
Maslovₙ-computes n p = maslov-computes (standardᴹ n p)

Maslovₙ-spec : (n : ℕ) (p : 3 ≤ n) →
               ⟦ Maslovₙ n p ⟧ ≋[ anc (standardᴹ n p) ]₀*
                 toffoliᴹˢ (standardᴹ n p)
Maslovₙ-spec n p = maslov-spec (standardᴹ n p)

Maslovₙ-clean : (n : ℕ) (p : 3 ≤ n) → ∀ x z →
                Clean (anc (standardᴹ n p)) x →
                (i : Fin ⌊ n ∸ 2 /2⌋) → z (anc (standardᴹ n p) i) ≡ true →
                amp ⟦ Maslovₙ n p ⟧ x z ≐ 0ᴬ
Maslovₙ-clean n p = maslov-clean (standardᴹ n p)

Maslovₙ-set0 : (n : ℕ) (p : 3 ≤ n) →
               set0ˢ (anc (standardᴹ n p)) ⟦ Maslovₙ n p ⟧ ≋
               set0ˢ (anc (standardᴹ n p)) (toffoliᴹˢ (standardᴹ n p))
Maslovₙ-set0 n p = maslov-set0 (standardᴹ n p)


------------------------------------------------------------------------
-- Resources

-- The parity of a number, 0 or 1.

parity : ℕ → ℕ
parity zero          = 0
parity (suc zero)    = 1
parity (suc (suc m)) = parity m

-- The number of wires a circuit acts on.

width : Circuit N → ℕ
width {N} _ = N

private
  -- One more level of the recursion adds a Toffoli-4 gate and its
  -- inverse, g of a resource each, to the count r of the rest.

  level : ∀ g j r → g + ((j * (g + g) + r) + g) ≡ suc j * (g + g) + r
  level = solve 3 (λ g j r → g :+ ((j :* (g :+ g) :+ r) :+ g)
                             := (con 1 :+ j) :* (g :+ g) :+ r) refl

-- ⌊m/2⌋ levels, each with two Toffoli-4 gates of four Hadamards, and
-- the middle gate: none for the CNOT (m even), two for the Toffoli
-- gate (m odd).  One path variable per Hadamard.

maslov-norm : (L : Layout N m) → norm (maslov L) ≡ ⌊ m /2⌋ * 8 + parity m * 2
maslov-norm {m = zero}        L = refl
maslov-norm {m = suc zero}    L = refl
maslov-norm {m = suc (suc m)} L =
  trans (norm-++ G (maslov (inner L) ++ G †))
    (trans (cong (4 +_) (trans (norm-++ (maslov (inner L)) (G †))
                               (cong (_+ 4) (maslov-norm (inner L)))))
           (level 4 ⌊ m /2⌋ (parity m * 2)))
  where
  G : Circuit _
  G = rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L) (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L)

maslov-paths : (L : Layout N m) →
               paths (maslov L) ≡ ⌊ m /2⌋ * 8 + parity m * 2
maslov-paths L = trans (paths≡norm (maslov L)) (maslov-norm L)

-- Eight T or T† gates in each Toffoli-4 gate, seven in the Toffoli
-- circuit, none in the CNOT.

maslov-tcount : (L : Layout N m) →
                tcount (maslov L) ≡ ⌊ m /2⌋ * 16 + parity m * 7
maslov-tcount {m = zero}        L = refl
maslov-tcount {m = suc zero}    L = refl
maslov-tcount {m = suc (suc m)} L =
  trans (tcount-++ G (maslov (inner L) ++ G †))
    (trans (cong (8 +_) (trans (tcount-++ (maslov (inner L)) (G †))
                               (cong (_+ 8) (maslov-tcount (inner L)))))
           (level 8 ⌊ m /2⌋ (parity m * 7)))
  where
  G : Circuit _
  G = rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L) (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L)

-- Ten Clifford gates (four H, six CNOT) in each Toffoli-4 gate, nine
-- (two H, seven CNOT) in the tool's Toffoli circuit, one in the CNOT.

maslov-cliffords : (L : Layout N m) →
                   cliffords (maslov L) ≡ ⌊ m /2⌋ * 20 + (parity m * 8 + 1)
maslov-cliffords {m = zero}        L = refl
maslov-cliffords {m = suc zero}    L = refl
maslov-cliffords {m = suc (suc m)} L =
  trans (cliffords-++ G (maslov (inner L) ++ G †))
    (trans (cong (10 +_) (trans (cliffords-++ (maslov (inner L)) (G †))
                               (cong (_+ 10) (maslov-cliffords (inner L)))))
           (level 10 ⌊ m /2⌋ (parity m * 8 + 1)))
  where
  G : Circuit _
  G = rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L) (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L)

-- On the paper's layout, with ⌈(n − 3)/2⌉ ancillas and n's parity.

Maslovₙ-paths : (n : ℕ) (p : 3 ≤ n) →
                paths (Maslovₙ n p) ≡ ⌈ n ∸ 3 /2⌉ * 8 + parity n * 2
Maslovₙ-paths (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) =
  maslov-paths (layout (suc m))

Maslovₙ-tcount : (n : ℕ) (p : 3 ≤ n) →
                 tcount (Maslovₙ n p) ≡ ⌈ n ∸ 3 /2⌉ * 16 + parity n * 7
Maslovₙ-tcount (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) =
  maslov-tcount (layout (suc m))

Maslovₙ-cliffords : (n : ℕ) (p : 3 ≤ n) →
                    cliffords (Maslovₙ n p) ≡
                    ⌈ n ∸ 3 /2⌉ * 20 + (parity n * 8 + 1)
Maslovₙ-cliffords (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) =
  maslov-cliffords (layout (suc m))

-- In closed form.  ⌊m/2⌋ pairs of controls and the parity make up m
-- (halves), so the circuit has 4m path variables, 8m T gates and
-- 10m + 1 Clifford gates when m is even, and 2, 1 and 2 fewer when m is
-- odd.  With m = n − 2: for even n, 4(n − 2), 8(n − 2) = 8n − 16 and
-- 10(n − 2) + 1; for odd n, 8n − 17 T gates and 10n − 21 Clifford
-- gates.

halves : ∀ m → ⌊ m /2⌋ * 2 + parity m ≡ m
halves zero          = refl
halves (suc zero)    = refl
halves (suc (suc m)) = cong (λ k → suc (suc k)) (halves m)

maslov-paths-closed : (L : Layout N m) →
                      paths (maslov L) + 2 * parity m ≡ 4 * m
maslov-paths-closed {m = m} L =
  trans (cong (_+ 2 * parity m) (maslov-paths L))
    (trans (shape ⌊ m /2⌋ (parity m)) (cong (4 *_) (halves m)))
  where
  shape : ∀ j p → (j * 8 + p * 2) + 2 * p ≡ 4 * (j * 2 + p)
  shape = solve 2 (λ j p → (j :* con 8 :+ p :* con 2) :+ con 2 :* p
                           := con 4 :* (j :* con 2 :+ p)) refl

maslov-tcount-closed : (L : Layout N m) →
                       tcount (maslov L) + parity m ≡ 8 * m
maslov-tcount-closed {m = m} L =
  trans (cong (_+ parity m) (maslov-tcount L))
    (trans (shape ⌊ m /2⌋ (parity m)) (cong (8 *_) (halves m)))
  where
  shape : ∀ j p → (j * 16 + p * 7) + p ≡ 8 * (j * 2 + p)
  shape = solve 2 (λ j p → (j :* con 16 :+ p :* con 7) :+ p
                           := con 8 :* (j :* con 2 :+ p)) refl

maslov-cliffords-closed : (L : Layout N m) →
                          cliffords (maslov L) + 2 * parity m ≡ 10 * m + 1
maslov-cliffords-closed {m = m} L =
  trans (cong (_+ 2 * parity m) (maslov-cliffords L))
    (trans (shape ⌊ m /2⌋ (parity m)) (cong (λ k → 10 * k + 1) (halves m)))
  where
  shape : ∀ j p → (j * 20 + (p * 8 + 1)) + 2 * p ≡ 10 * (j * 2 + p) + 1
  shape = solve 2 (λ j p → (j :* con 20 :+ (p :* con 8 :+ con 1))
                           :+ con 2 :* p
                           := con 10 :* (j :* con 2 :+ p) :+ con 1) refl

Maslovₙ-paths-closed : (n : ℕ) (p : 3 ≤ n) →
                       paths (Maslovₙ n p) + 2 * parity n ≡ 4 * (n ∸ 2)
Maslovₙ-paths-closed (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) =
  maslov-paths-closed (layout (suc m))

Maslovₙ-tcount-closed : (n : ℕ) (p : 3 ≤ n) →
                        tcount (Maslovₙ n p) + parity n ≡ 8 * (n ∸ 2)
Maslovₙ-tcount-closed (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) =
  maslov-tcount-closed (layout (suc m))

Maslovₙ-cliffords-closed : (n : ℕ) (p : 3 ≤ n) →
                           cliffords (Maslovₙ n p) + 2 * parity n ≡
                           10 * (n ∸ 2) + 1
Maslovₙ-cliffords-closed (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) =
  maslov-cliffords-closed (layout (suc m))


------------------------------------------------------------------------
-- Qubits

-- The circuit touches every control, the target and every ancilla of
-- its layout.  With three or more controls, the first Toffoli-4 gate
-- touches c₀, c₁, c₂ and a₀, and the inner construction touches the
-- rest; with fewer the middle gate touches them all.

private
  -- Where a wire of the first gate, or of the inner construction, sits
  -- in the circuit.

  in-gate : (L : Layout N (suc (suc m))) {u : Fin N} →
            u ∈ c₀ L ∷ c₁ L ∷ c₂ L ∷ a₀ L ∷ [] → u ∈ᶜ maslov L
  in-gate L p =
    ∈ᶜ-++ˡ G (maslov (inner L) ++ G †)
           (∈ᶜ-rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L)
                    (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L) p)
    where
    G : Circuit _
    G = rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L) (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L)

  in-inner : (L : Layout N (suc (suc m))) {u : Fin N} →
             u ∈ᶜ maslov (inner L) → u ∈ᶜ maslov L
  in-inner L p =
    ∈ᶜ-++ʳ G (maslov (inner L) ++ G †) (∈ᶜ-++ˡ (maslov (inner L)) (G †) p)
    where
    G : Circuit _
    G = rc3x (c₀ L) (c₁ L) (c₂ L) (a₀ L) (c₀≢a₀ L) (c₁≢a₀ L) (c₂≢a₀ L)

  in-middle : (L : Layout N (suc zero)) {u : Fin N} →
              u ∈ ctl L zero ∷ ctl L (suc zero) ∷ tgt L ∷ [] →
              u ∈ᶜ maslov L
  in-middle L =
    ∈ᶜ-tof₃ (ctl L zero) (ctl L (suc zero)) (tgt L) (c₀≢c₁ L)
            (ctl≢tgt L zero) (ctl≢tgt L (suc zero))

maslov-ctl : (L : Layout N m) (i : Fin (suc m)) → ctl L i ∈ᶜ maslov L
maslov-ctl {m = zero}        L zero                = here (here refl)
maslov-ctl {m = zero}        L (suc ())
maslov-ctl {m = suc zero}    L zero                = in-middle L (here refl)
maslov-ctl {m = suc zero}    L (suc zero)          =
  in-middle L (there (here refl))
maslov-ctl {m = suc zero}    L (suc (suc ()))
maslov-ctl {m = suc (suc m)} L zero                = in-gate L (here refl)
maslov-ctl {m = suc (suc m)} L (suc zero)          =
  in-gate L (there (here refl))
maslov-ctl {m = suc (suc m)} L (suc (suc zero))    =
  in-gate L (there (there (here refl)))
maslov-ctl {m = suc (suc m)} L (suc (suc (suc i))) =
  in-inner L (maslov-ctl (inner L) (suc i))

maslov-tgt : (L : Layout N m) → tgt L ∈ᶜ maslov L
maslov-tgt {m = zero}        L = here (there (here refl))
maslov-tgt {m = suc zero}    L = in-middle L (there (there (here refl)))
maslov-tgt {m = suc (suc m)} L = in-inner L (maslov-tgt (inner L))

maslov-anc : (L : Layout N m) (j : Fin ⌊ m /2⌋) → anc L j ∈ᶜ maslov L
maslov-anc {m = zero}        L ()
maslov-anc {m = suc zero}    L ()
maslov-anc {m = suc (suc m)} L zero    =
  in-gate L (there (there (there (here refl))))
maslov-anc {m = suc (suc m)} L (suc j) = in-inner L (maslov-anc (inner L) j)

-- So when the layout's wires are all the wires, no wire is idle, and
-- the circuit's qubits, counted as the tool counts them, are all its
-- wires.

maslov-touched : (L : Layout N m) →
                 (∀ u → (∃ λ i → u ≡ ctl L i) ⊎ u ≡ tgt L ⊎
                        (∃ λ j → u ≡ anc L j)) →
                 ∀ u → u ∈ᶜ maslov L
maslov-touched L cover u = touch (cover u)
  where
  touch : ((∃ λ i → u ≡ ctl L i) ⊎ u ≡ tgt L ⊎ (∃ λ j → u ≡ anc L j)) →
          u ∈ᶜ maslov L
  touch (inj₁ (i , refl))        = maslov-ctl L i
  touch (inj₂ (inj₁ refl))       = maslov-tgt L
  touch (inj₂ (inj₂ (j , refl))) = maslov-anc L j

maslov-qubits : (L : Layout N m) →
                (∀ u → (∃ λ i → u ≡ ctl L i) ⊎ u ≡ tgt L ⊎
                       (∃ λ j → u ≡ anc L j)) →
                qubits (maslov L) ≡ N
maslov-qubits L cover = qubits-all (maslov L) (maslov-touched L cover)

-- On the paper's layout, for every n ≥ 3: every one of the
-- n + ⌈(n − 3)/2⌉ wires is touched.

Maslovₙ-touched : (n : ℕ) (p : 3 ≤ n) (u : Fin (n + ⌈ n ∸ 3 /2⌉)) →
                  u ∈ᶜ Maslovₙ n p
Maslovₙ-touched n p = maslov-touched (standardᴹ n p) (standardᴹ-wires n p)

Maslovₙ-qubits : (n : ℕ) (p : 3 ≤ n) →
                 qubits (Maslovₙ n p) ≡ n + ⌈ n ∸ 3 /2⌉
Maslovₙ-qubits n p =
  maslov-qubits (standardᴹ n p) (standardᴹ-wires n p)


------------------------------------------------------------------------
-- Table 2

-- Maslov50 and Maslov100: 74 and 149 qubits, 192 and 392 path
-- variables, 481 and 981 Clifford gates, 384 and 784 T gates.  (The
-- circuits are not computed: these are the counts above at n = 50 and
-- n = 100.  The qubits are the wires the gates touch, as the tool
-- counts them; the width is the same number, by definition.)

table-2-Maslov50 : (p : 3 ≤ 50) →
                   (qubits (Maslovₙ 50 p) ≡ 74)
                   × (paths (Maslovₙ 50 p) ≡ 192)
                   × (cliffords (Maslovₙ 50 p) ≡ 481)
                   × (tcount (Maslovₙ 50 p) ≡ 384)
table-2-Maslov50 p =
  Maslovₙ-qubits 50 p , Maslovₙ-paths 50 p , Maslovₙ-cliffords 50 p
  , Maslovₙ-tcount 50 p

table-2-Maslov100 : (p : 3 ≤ 100) →
                    (qubits (Maslovₙ 100 p) ≡ 149)
                    × (paths (Maslovₙ 100 p) ≡ 392)
                    × (cliffords (Maslovₙ 100 p) ≡ 981)
                    × (tcount (Maslovₙ 100 p) ≡ 784)
table-2-Maslov100 p =
  Maslovₙ-qubits 100 p , Maslovₙ-paths 100 p , Maslovₙ-cliffords 100 p
  , Maslovₙ-tcount 100 p


------------------------------------------------------------------------
-- The circuits for n = 4, 5 and 6

-- n = 4, on 5 wires: a ⊕= x₀x₁x₂ (a = wire 4), t ⊕= a (t = wire 3), and
-- the first gate undone.

Maslov-4 : Maslovₙ 4 (s≤s (s≤s (s≤s z≤n))) ≡
           rc3x (# 0) (# 1) (# 2) (# 4) _ _ _
           ++ CNOT (# 4) (# 3) _ ∷ []
           ++ rc3x (# 0) (# 1) (# 2) (# 4) _ _ _ †
Maslov-4 = refl

-- n = 5, on 6 wires: a ⊕= x₀x₁x₂ (a = wire 5), t ⊕= a x₃ (t = wire 4),
-- by the tool's Toffoli circuit, and the first gate undone.  (That
-- circuit uses the proof that its first control is not its target only
-- under a λ, where unification cannot recover it, so it is written
-- out: it is the inner layout's.)

Maslov-5 : Maslovₙ 5 (s≤s (s≤s (s≤s z≤n))) ≡
           rc3x (# 0) (# 1) (# 2) (# 5) _ _ _
           ++ tof₃ (# 5) (# 3) (# 4) _
                   (ctl≢tgt (inner (standardᴹ 5 (s≤s (s≤s (s≤s z≤n))))) zero)
                   _
           ++ rc3x (# 0) (# 1) (# 2) (# 5) _ _ _ †
Maslov-5 = refl

-- n = 6, on 8 wires: a₀ ⊕= x₀x₁x₂, a₁ ⊕= a₀x₃x₄, t ⊕= a₁ (a₀, a₁ =
-- wires 6, 7; t = wire 5), then a₁ and a₀ uncomputed.

Maslov-6 : Maslovₙ 6 (s≤s (s≤s (s≤s z≤n))) ≡
           rc3x (# 0) (# 1) (# 2) (# 6) _ _ _
           ++ (rc3x (# 6) (# 3) (# 4) (# 7) _ _ _
               ++ CNOT (# 7) (# 5) _ ∷ []
               ++ rc3x (# 6) (# 3) (# 4) (# 7) _ _ _ †)
           ++ rc3x (# 0) (# 1) (# 2) (# 6) _ _ _ †
Maslov-6 = refl
