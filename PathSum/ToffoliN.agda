------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-bit Toffoli gate with n − 3 ancillas, for every n (Amy, QPL
-- 2018, section 5.2)
--
-- Section 5.2 verifies Clifford+T implementations of
--
--    Toffoli_n : |x₁ x₂ … x_n⟩ ↦ |x₁ x₂ … (x_n ⊕ x₁ x₂ ⋯ x_(n−1))⟩
--
-- "using the standard decomposition into 2(n − 3) + 1 Toffoli gates
-- and n − 3 ancillas", up to n = 100, each instance by computation.
-- Here the decomposition is proved correct for every n ≥ 3 at once.
--
-- The circuit.  On a layout L (PathSum.ToffoliN.Chain: j + 2 controls,
-- a target and j ancillas, n = j + 3) the netlist is the V-chain
-- chain L -- compute a₀ = c₀c₁, a₁ = a₀c₂, …, flip the target, then
-- uncompute -- and the circuit tofₙ L expands each of its 2j + 1
-- Toffoli gates into the seven-T circuit of PathSum.Toffoli
-- (PathSum.Toffoli.Netlist).  Toffoliₙ n is tofₙ on the paper's layout,
-- n + (n − 3) wires: the controls are wires 0 … n − 2, the target wire
-- n − 1, the ancillas wires n … 2n − 4.
--
-- The theorem.  An ancilla enters in |0⟩, so the claim concerns the
-- columns of the operator at the inputs whose ancillas read 0 (clean
-- inputs), and says that there the circuit is Toffoli_n and "leaves
-- the ancillas clean":
--
--    ⟦ tofₙ L ⟧ ≋[ anc L ]₀* toffoliₙˢ L                    (tofₙ-spec)
--
-- (PathSum.Ancillas: from a clean input, the normalised amplitudes of
-- the circuit are those of the specification), toffoliₙˢ L being the
-- classical path-sum that flips the target by the lift of
-- x_c₀ x_c₁ ⋯ x_c(j+1) and outputs every other input unchanged -- the
-- ancillas included, so from a clean input no amplitude reaches an
-- output with an ancilla at 1 (tofₙ-clean).  Equivalently, with the
-- ancillas read as the constant 0 in the polynomials of both sides --
-- how the paper treats an ancilla initialised to |0⟩ -- the two
-- path-sums are ≋ outright (tofₙ-set0).  Toffoliₙ-spec,
-- Toffoliₙ-clean and Toffoliₙ-set0 are the same for the paper's
-- layout, for every n ≥ 3.
-- Stated on all columns, the circuit computes the permutation of its
-- netlist (tofₙ-computes); off the clean inputs that permutation is
-- not Toffoli_n, which is why the theorem is restricted.
--
-- The proof composes, where the paper's tool reduces.  The paper's
-- verifier builds the path-sum of the whole circuit and reduces it by
-- the rules of figure 2 to the specification with the ancillas set to
-- 0.  Here each Toffoli gate's path-sum is already known to be the
-- classical Toffoli path-sum (PathSum.Toffoli.tof-computes); by
-- proposition 2.7 a composite of path-sums computing Boolean functions
-- computes the composite function (PathSum.Classical.⟦++⟧-computes),
-- so the circuit computes the netlist's function (expand-computes);
-- and that function is Toffoli_n on clean inputs, by induction on the
-- number of ancillas (PathSum.ToffoliN.Chain.chain-correct).  No path-sum
-- of the whole circuit is ever computed, and no closed instance is
-- evaluated, so the statement costs the same for every n.  (A ≋
-- statement about a concrete composite of Toffoli circuits is what
-- this development avoids: Agda compares such statements by unfolding
-- them into amplitudes -- see PathSum.Toffoli.tof-tof.)
--
-- Resources.  The circuit uses 2(n − 3) + 1 Toffoli gates
-- (Toffoliₙ-gates) on n + (n − 3) wires; each contributes two
-- Hadamards, hence two path variables, and seven T or T† gates, so
-- Toffoliₙ has (2(n − 3) + 1) · 2 path variables (Toffoliₙ-paths) and
-- (2(n − 3) + 1) · 7 T gates (Toffoliₙ-tcount).  At n = 50 and n = 100
-- that is 97 and 197 qubits, 190 and 390 path variables, 665 and 1365
-- T gates: the paper's table 2, rows Toffoli50 and Toffoli100
-- (table-2-Toffoli50, table-2-Toffoli100).  Its Clifford counts, 855
-- and 1755, are nine per Toffoli gate (95·9, 195·9): exactly the
-- Clifford count of Nielsen and Chuang's figure 4.9 circuit, whose T†
-- and S on the second control the circuit here merges into one T,
-- leaving eight.  So the table is consistent with that circuit; the
-- Clifford column is not formalised.  Finally the netlists for n = 4 and n = 5
-- are displayed (netlist-4, netlist-5), as a check that chain is the
-- standard V-chain.
--
-- Not formalised: the Maslov decomposition with relative-phase
-- Toffoli gates (section 5.2's second implementation), and the
-- verifier's own run on these circuits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.ToffoliN (M₀ : ℕ) where

open import Data.Bool.Base using (true; false)
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; map; length)
open import Data.Nat.Base using (_+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong)

open import PathSum.Ancillas M₀ using
  (Clean; set0ˢ; _≋[_]₀*_; ≋[]₀*⇔set0ˢ; computes⇒≋[]₀*; clean-ancillas)
open import PathSum.Classical M₀ using
  (_computes_; classical-computes; computes-≗; setWire; outBit-none)
open import PathSum.CRK.Path M₀ using (Circuit; ⟦_⟧; paths)
open import PathSum.Cyclotomic M₀ using (_≐_; 0ᴬ)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Polynomial.Boolean using (liftᵉ)
open import PathSum.Toffoli.Netlist M₀ using
  (Toff; expand; apply; expand-computes; paths-expand; tcount;
   tcount-expand)
open import PathSum.ToffoliN.Chain M₀ using
  (Layout; tgt; anc; chain; length-chain; toffoliₙ; toffoliₙᵉ;
   toffoliₙˢ; fun-toffoliₙˢ; chain-correct; toffoliₙ-anc; standard)

import PathSum.Toffoli.Netlist M₀ as Netlist

private
  variable
    N j : ℕ


------------------------------------------------------------------------
-- The circuit on any layout

-- The V-chain, each Toffoli gate expanded into the seven-T circuit.

tofₙ : Layout N j → Circuit N
tofₙ L = expand (chain L)

-- On all inputs it computes the permutation of its netlist.

tofₙ-computes : (L : Layout N j) → ⟦ tofₙ L ⟧ computes apply (chain L)
tofₙ-computes L = expand-computes (chain L)

-- The specification computes Toffoli_n; the two agree on clean inputs.

toffoliₙˢ-computes : (L : Layout N j) → toffoliₙˢ L computes toffoliₙ L
toffoliₙˢ-computes L =
  computes-≗ (toffoliₙˢ L) (fun-toffoliₙˢ L)
    (classical-computes (setWire (tgt L) (liftᵉ (toffoliₙᵉ L))))

tofₙ-spec : (L : Layout N j) → ⟦ tofₙ L ⟧ ≋[ anc L ]₀* toffoliₙˢ L
tofₙ-spec L =
  computes⇒≋[]₀* ⟦ tofₙ L ⟧ (toffoliₙˢ L) (anc L)
    (tofₙ-computes L) (toffoliₙˢ-computes L) (chain-correct L)

-- The ancillas are left clean: from a clean input, no amplitude
-- reaches an output with an ancilla at 1.

tofₙ-clean : (L : Layout N j) → ∀ x z → Clean (anc L) x →
             (i : Fin j) → z (anc L i) ≡ true →
             amp ⟦ tofₙ L ⟧ x z ≐ 0ᴬ
tofₙ-clean L = clean-ancillas (anc L) (tofₙ-spec L) out0
  where
  out0 : ∀ x (y : Assign 0) → Clean (anc L) x →
         ∀ i → outBit (toffoliₙˢ L) x y (anc L i) ≡ false
  out0 x y cl i = trans (outBit-none (toffoliₙˢ L) x y (anc L i))
    (trans (fun-toffoliₙˢ L x (anc L i)) (toffoliₙ-anc L x cl i))

-- With the ancillas read as the constant 0 on both sides, the circuit's
-- path-sum is equivalent to the specification's.

tofₙ-set0 : (L : Layout N j) →
            set0ˢ (anc L) ⟦ tofₙ L ⟧ ≋ set0ˢ (anc L) (toffoliₙˢ L)
tofₙ-set0 L =
  Equivalence.to (≋[]₀*⇔set0ˢ (anc L) ⟦ tofₙ L ⟧ (toffoliₙˢ L))
                 (tofₙ-spec L)


------------------------------------------------------------------------
-- The paper's circuit, for every n ≥ 3

-- On n + (n − 3) wires: controls 0 … n − 2, target n − 1, ancillas
-- n … 2n − 4 (PathSum.ToffoliN.Chain.standard).

Toffoliₙ : (n : ℕ) → 3 ≤ n → Circuit (n + (n ∸ 3))
Toffoliₙ n p = tofₙ (standard n p)

Toffoliₙ-computes : (n : ℕ) (p : 3 ≤ n) →
                    ⟦ Toffoliₙ n p ⟧ computes apply (chain (standard n p))
Toffoliₙ-computes n p = tofₙ-computes (standard n p)

Toffoliₙ-spec : (n : ℕ) (p : 3 ≤ n) →
                ⟦ Toffoliₙ n p ⟧ ≋[ anc (standard n p) ]₀*
                  toffoliₙˢ (standard n p)
Toffoliₙ-spec n p = tofₙ-spec (standard n p)

Toffoliₙ-clean : (n : ℕ) (p : 3 ≤ n) → ∀ x z →
                 Clean (anc (standard n p)) x → (i : Fin (n ∸ 3)) →
                 z (anc (standard n p) i) ≡ true →
                 amp ⟦ Toffoliₙ n p ⟧ x z ≐ 0ᴬ
Toffoliₙ-clean n p = tofₙ-clean (standard n p)

Toffoliₙ-set0 : (n : ℕ) (p : 3 ≤ n) →
                set0ˢ (anc (standard n p)) ⟦ Toffoliₙ n p ⟧ ≋
                set0ˢ (anc (standard n p)) (toffoliₙˢ (standard n p))
Toffoliₙ-set0 n p =
  Equivalence.to (≋[]₀*⇔set0ˢ (anc (standard n p)) ⟦ Toffoliₙ n p ⟧
                              (toffoliₙˢ (standard n p)))
                 (Toffoliₙ-spec n p)


------------------------------------------------------------------------
-- Resources, and table 2

-- 2(n − 3) + 1 Toffoli gates, two path variables and seven T gates
-- each.

Toffoliₙ-gates : (n : ℕ) (p : 3 ≤ n) →
                 length (chain (standard n p)) ≡ 2 * (n ∸ 3) + 1
Toffoliₙ-gates n p = length-chain (standard n p)

Toffoliₙ-paths : (n : ℕ) (p : 3 ≤ n) →
                 paths (Toffoliₙ n p) ≡ (2 * (n ∸ 3) + 1) * 2
Toffoliₙ-paths n p = trans (paths-expand (chain (standard n p)))
                           (cong (_* 2) (Toffoliₙ-gates n p))

Toffoliₙ-tcount : (n : ℕ) (p : 3 ≤ n) →
                  tcount (Toffoliₙ n p) ≡ (2 * (n ∸ 3) + 1) * 7
Toffoliₙ-tcount n p = trans (tcount-expand (chain (standard n p)))
                            (cong (_* 7) (Toffoliₙ-gates n p))

-- Toffoli50 and Toffoli100: 97 and 197 qubits, 190 and 390 path
-- variables, 665 and 1365 T gates.  (The circuits are not computed:
-- these are the counts above at n = 50 and n = 100.)

table-2-Toffoli50 : (p : 3 ≤ 50) →
                    (50 + (50 ∸ 3) ≡ 97) × (paths (Toffoliₙ 50 p) ≡ 190)
                    × (tcount (Toffoliₙ 50 p) ≡ 665)
table-2-Toffoli50 p = refl , Toffoliₙ-paths 50 p , Toffoliₙ-tcount 50 p

table-2-Toffoli100 : (p : 3 ≤ 100) →
                     (100 + (100 ∸ 3) ≡ 197)
                     × (paths (Toffoliₙ 100 p) ≡ 390)
                     × (tcount (Toffoliₙ 100 p) ≡ 1365)
table-2-Toffoli100 p =
  refl , Toffoliₙ-paths 100 p , Toffoliₙ-tcount 100 p


------------------------------------------------------------------------
-- The netlists for n = 4 and n = 5

-- Each gate as (control, control, target).

toff-wires : Toff N → Fin N × Fin N × Fin N
toff-wires g = Netlist.Toff.c₁ g , Netlist.Toff.c₂ g , Netlist.Toff.t g

-- n = 4, on 5 wires: a ⊕= x₀x₁ (a = wire 4), t ⊕= a x₂ (t = wire 3),
-- a ⊕= x₀x₁.

netlist-4 :
  map toff-wires (chain (standard 4 (s≤s (s≤s (s≤s z≤n))))) ≡
  (# 0 , # 1 , # 4) ∷ (# 4 , # 2 , # 3) ∷ (# 0 , # 1 , # 4) ∷ []
netlist-4 = refl

-- n = 5, on 7 wires: a₀ ⊕= x₀x₁, a₁ ⊕= a₀x₂, t ⊕= a₁x₃, then a₁ and a₀
-- uncomputed (a₀, a₁ = wires 5, 6; t = wire 4).

netlist-5 :
  map toff-wires (chain (standard 5 (s≤s (s≤s (s≤s z≤n))))) ≡
  (# 0 , # 1 , # 5) ∷ (# 5 , # 2 , # 6) ∷ (# 6 , # 3 , # 4) ∷
  (# 5 , # 2 , # 6) ∷ (# 0 , # 1 , # 5) ∷ []
netlist-5 = refl
