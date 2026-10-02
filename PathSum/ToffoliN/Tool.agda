------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-bit Toffoli gate exactly as the paper's tool builds it, for
-- every n (Amy, QPL 2018, section 5.2 and table 2)
--
-- Section 5.2 verifies "the standard decomposition into 2(n − 3) + 1
-- Toffoli gates and n − 3 ancillas" up to n = 100, and table 2 lists
-- the resources of the circuits verified at n = 50 and n = 100.  The
-- paper's tool, Feynman (github.com/meamy/feynman), builds them by
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
-- This is the V-chain of PathSum.ToffoliN.Chain -- a₀ ⊕= x₀ x₁ first
-- and uncomputed last, the chain on a₀ and the remaining wires between
-- -- but with each Toffoli gate written out by the tool's own
-- sixteen-gate circuit toffoli (PathSum.Toffoli.Depth3's tof₃: seven
-- T gates, two Hadamards and seven CNOTs), and the uncomputing one by
-- that circuit's adjoint (the tool's dagger = reverse . map daggerGate,
-- PathSum.CRK.Adjoint's _†), where PathSum.ToffoliN writes every
-- Toffoli gate with PathSum.Toffoli's fifteen-gate tof.  Here it is on
-- any layout L (j + 2 controls, a target and j ancillas):
--
--    toffoliNᶜ L = tof₃ c₀ c₁ t                               (j = 0)
--    toffoliNᶜ L = subproduct L ++ toffoliNᶜ (inner L)
--                  ++ subproduct L †                         (j + 1)
--
-- with subproduct L = tof₃ c₀ c₁ a₀, and ToffoliNᶜ n is it on the
-- paper's layout (PathSum.ToffoliN.Chain.standard: controls 0 … n − 2,
-- target n − 1, ancillas from n on -- verifyToffoliN's numbering of
-- its variables).  The tool's two-wire case, a CNOT, does not arise
-- for n ≥ 3.  That this is the tool's list gate for gate, for every
-- n ≥ 3, is PathSum.ToffoliN.Feynman.
--
-- What it computes.  On every input it computes the netlist's Boolean
-- function apply (chain L) (toffoliNᶜ-computes, by induction on the
-- layout): the tool's Toffoli circuit computes the Toffoli function
-- (PathSum.Toffoli.Depth3.tof₃-computes), so does its adjoint, the
-- Toffoli function being an involution (PathSum.Adder.Feynman.
-- tof₃†-computes, by PathSum.Classical.Adjoint.†-involution), and by
-- proposition 2.7 a composite computes the composite function
-- (PathSum.Classical.⟦++⟧-computes).  So what PathSum.ToffoliN proves
-- of its circuit holds of this one, by the same argument: on the
-- inputs whose ancillas read 0 it is Toffoli_n (toffoliNᶜ-spec), it
-- leaves the ancillas clean (toffoliNᶜ-clean), and with the ancillas
-- read as the constant 0 the path-sums are ≋ (toffoliNᶜ-set0) -- the
-- statement the tool checks, its toffoliNSpec setting the ancillas'
-- inputs to 0 -- and on the paper's layout for every n ≥ 3
-- (ToffoliNᶜ-spec, ToffoliNᶜ-clean, ToffoliNᶜ-set0).  As both compute
-- the same function on every input, its path-sum is ≋ that of
-- PathSum.ToffoliN's circuit (toffoliNᶜ-≋, ToffoliNᶜ-≋).  No path-sum
-- of the whole circuit is computed and no closed instance evaluated.
--
-- Resources.  Per Toffoli gate of the chain, the tool's Toffoli
-- circuit and its adjoint have two Hadamards, hence two path
-- variables, seven T or T† gates and nine Clifford gates (inverting
-- keeps all three: PathSum.CRK.Adjoint.norm-†, PathSum.Adder.Feynman.
-- tcount-† and cliffords-†), so the circuit has (2(n − 3) + 1) · 2
-- path variables, (2(n − 3) + 1) · 9 Clifford gates and
-- (2(n − 3) + 1) · 7 T gates (ToffoliNᶜ-paths, ToffoliNᶜ-cliffords,
-- ToffoliNᶜ-tcount).  It touches every one of its n + (n − 3) wires,
-- so its qubits as the tool counts them (PathSum.CRK.Qubits.qubits,
-- the number of distinct wires printVerStats collects) are
-- n + (n − 3) (ToffoliNᶜ-qubits).  At n = 50 and n = 100 these are
-- table 2's rows in all four columns, each counted from the circuit
-- (Toffoli50ᵀ, Toffoli100ᵀ):
--
--                   qubits   path vars   Clifford     T
--      Toffoli50       97       190         855      665
--      Toffoli100     197       390        1755     1365
--
-- -- the numbers the tool's own printVerStats prints for its toffoliN
-- at n = 50 and n = 100, run under GHC.  (PathSum.ToffoliN's circuit
-- has the same rows but eight Clifford gates per Toffoli gate.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.ToffoliN.Tool (M₀ : ℕ) where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (_+_; _*_; _∸_; _≤_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adder.Feynman M₀ using
  (tof₃†-computes; tcount-†; cliffords-†)
open import PathSum.Adder.Tool M₀ using (∈ᶜ-tof₃)
open import PathSum.Ancillas M₀ using
  (Clean; set0ˢ; _≋[_]₀*_; ≋[]₀*⇔set0ˢ; computes⇒≋[]₀*; clean-ancillas)
open import PathSum.Classical M₀ using
  (_computes_; computes-≗; computes-≋; ⟦++⟧-computes; outBit-none)
open import PathSum.CRK.Adjoint M using (_†; norm-++; norm-†)
open import PathSum.CRK.Circuit M using (paths≡norm)
open import PathSum.CRK.Path M₀ using (Circuit; ⟦_⟧; norm; paths)
open import PathSum.CRK.Qubits M₀ using
  (_∈ᶜ_; ∈ᶜ-++ˡ; ∈ᶜ-++ʳ; qubits; qubits-all)
open import PathSum.Cyclotomic M₀ using (_≐_; 0ᴬ)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.QFT.Count M₀ using (cliffords; cliffords-++)
open import PathSum.Toffoli.Depth3 M₀ using (tof₃; tof₃-computes)
open import PathSum.Toffoli.Gate M₀ using (toffoli)
open import PathSum.Toffoli.Netlist M₀ using
  (apply; apply-++; tcount; tcount-++)
open import PathSum.ToffoliN M₀ using
  (tofₙ; tofₙ-computes; toffoliₙˢ-computes; Toffoliₙ)
open import PathSum.ToffoliN.Chain M₀ using
  (Layout; ctl; tgt; anc; c₀≢c₁; ctl≢tgt; ctl≢anc; inner; first; chain;
   toffoliₙˢ; fun-toffoliₙˢ; chain-correct; toffoliₙ-anc; standard)
open import PathSum.ToffoliN.Wires M₀ using
  (Covers; covered; standard-wires)

private
  variable
    N j : ℕ


------------------------------------------------------------------------
-- The circuit

-- The tool's subproduct: its Toffoli circuit a₀ ⊕= c₀ c₁, the first
-- gate of the chain.

subproduct : Layout N (suc j) → Circuit N
subproduct L =
  tof₃ (ctl L zero) (ctl L (suc zero)) (anc L zero) (c₀≢c₁ L)
       (ctl≢anc L zero zero) (ctl≢anc L (suc zero) zero)

-- Without ancillas the tool's Toffoli circuit onto the target; with
-- them the subproduct, the circuit on the inner layout, and the
-- subproduct's adjoint.

toffoliNᶜ : Layout N j → Circuit N
toffoliNᶜ {j = zero}  L =
  tof₃ (ctl L zero) (ctl L (suc zero)) (tgt L) (c₀≢c₁ L)
       (ctl≢tgt L zero) (ctl≢tgt L (suc zero))
toffoliNᶜ {j = suc j} L =
  subproduct L ++ toffoliNᶜ (inner L) ++ subproduct L †

-- On the paper's layout: n + (n − 3) wires, the controls 0 … n − 2,
-- the target n − 1, the ancillas n … 2n − 4.

ToffoliNᶜ : (n : ℕ) → 3 ≤ n → Circuit (n + (n ∸ 3))
ToffoliNᶜ n p = toffoliNᶜ (standard n p)


------------------------------------------------------------------------
-- What it computes

-- The subproduct computes the first gate's Toffoli function, and so
-- does its adjoint, that function being an involution.  (Stated with
-- the wires spelled as in subproduct: a path-sum ⟦ C ⟧ is only ever
-- compared with one of the same circuit, never unfolded.)

subproduct-computes :
  (L : Layout N (suc j)) →
  ⟦ subproduct L ⟧ computes
    toffoli (ctl L zero) (ctl L (suc zero)) (anc L zero)
subproduct-computes L =
  tof₃-computes (ctl L zero) (ctl L (suc zero)) (anc L zero) (c₀≢c₁ L)
                (ctl≢anc L zero zero) (ctl≢anc L (suc zero) zero)

subproduct†-computes :
  (L : Layout N (suc j)) →
  ⟦ subproduct L † ⟧ computes
    toffoli (ctl L zero) (ctl L (suc zero)) (anc L zero)
subproduct†-computes L =
  tof₃†-computes (ctl L zero) (ctl L (suc zero)) (anc L zero) (c₀≢c₁ L)
                 (ctl≢anc L zero zero) (ctl≢anc L (suc zero) zero)

-- The chain is the first gate, the inner chain and the first gate
-- again.

private
  chain-step : (L : Layout N (suc j)) → ∀ x w →
               toffoli (ctl L zero) (ctl L (suc zero)) (anc L zero)
                 (apply (chain (inner L))
                   (toffoli (ctl L zero) (ctl L (suc zero)) (anc L zero) x))
                 w ≡
               apply (chain L) x w
  chain-step L x w = sym (cong (λ y → y w)
    (apply-++ (chain (inner L)) (first L ∷ [])
              (toffoli (ctl L zero) (ctl L (suc zero)) (anc L zero) x)))

-- On every input, the netlist's function: the subproduct and its
-- adjoint both compute the first gate's Toffoli function, and the
-- circuit between them the inner chain's.

toffoliNᶜ-computes : (L : Layout N j) →
                     ⟦ toffoliNᶜ L ⟧ computes apply (chain L)
toffoliNᶜ-computes {j = zero}  L =
  tof₃-computes (ctl L zero) (ctl L (suc zero)) (tgt L) (c₀≢c₁ L)
                (ctl≢tgt L zero) (ctl≢tgt L (suc zero))
toffoliNᶜ-computes {j = suc j} L =
  computes-≗ ⟦ toffoliNᶜ L ⟧ (chain-step L)
    (⟦++⟧-computes (subproduct L) (toffoliNᶜ (inner L) ++ subproduct L †)
      (subproduct-computes L)
      (⟦++⟧-computes (toffoliNᶜ (inner L)) (subproduct L †)
        (toffoliNᶜ-computes (inner L)) (subproduct†-computes L)))

-- On the inputs whose ancillas read 0, Toffoli_n.

toffoliNᶜ-spec : (L : Layout N j) → ⟦ toffoliNᶜ L ⟧ ≋[ anc L ]₀* toffoliₙˢ L
toffoliNᶜ-spec L =
  computes⇒≋[]₀* ⟦ toffoliNᶜ L ⟧ (toffoliₙˢ L) (anc L)
    (toffoliNᶜ-computes L) (toffoliₙˢ-computes L) (chain-correct L)

-- The ancillas are left clean: from a clean input, no amplitude
-- reaches an output with an ancilla at 1.

toffoliNᶜ-clean : (L : Layout N j) → ∀ x z → Clean (anc L) x →
                  (i : Fin j) → z (anc L i) ≡ true →
                  amp ⟦ toffoliNᶜ L ⟧ x z ≐ 0ᴬ
toffoliNᶜ-clean L = clean-ancillas (anc L) (toffoliNᶜ-spec L) out0
  where
  out0 : ∀ x (y : Assign 0) → Clean (anc L) x →
         ∀ i → outBit (toffoliₙˢ L) x y (anc L i) ≡ false
  out0 x y cl i = trans (outBit-none (toffoliₙˢ L) x y (anc L i))
    (trans (fun-toffoliₙˢ L x (anc L i)) (toffoliₙ-anc L x cl i))

-- With the ancillas read as the constant 0 on both sides, as the tool
-- reads them, the path-sums are equivalent.

toffoliNᶜ-set0 : (L : Layout N j) →
                 set0ˢ (anc L) ⟦ toffoliNᶜ L ⟧ ≋ set0ˢ (anc L) (toffoliₙˢ L)
toffoliNᶜ-set0 L =
  Equivalence.to (≋[]₀*⇔set0ˢ (anc L) ⟦ toffoliNᶜ L ⟧ (toffoliₙˢ L))
                 (toffoliNᶜ-spec L)

-- On every input, the path-sum of PathSum.ToffoliN's circuit.

toffoliNᶜ-≋ : (L : Layout N j) → ⟦ toffoliNᶜ L ⟧ ≋ ⟦ tofₙ L ⟧
toffoliNᶜ-≋ L =
  computes-≋ ⟦ toffoliNᶜ L ⟧ ⟦ tofₙ L ⟧ (toffoliNᶜ-computes L)
             (tofₙ-computes L)

-- The same on the paper's layout, for every n ≥ 3.

ToffoliNᶜ-computes : (n : ℕ) (p : 3 ≤ n) →
                     ⟦ ToffoliNᶜ n p ⟧ computes apply (chain (standard n p))
ToffoliNᶜ-computes n p = toffoliNᶜ-computes (standard n p)

ToffoliNᶜ-spec : (n : ℕ) (p : 3 ≤ n) →
                 ⟦ ToffoliNᶜ n p ⟧ ≋[ anc (standard n p) ]₀*
                   toffoliₙˢ (standard n p)
ToffoliNᶜ-spec n p = toffoliNᶜ-spec (standard n p)

ToffoliNᶜ-clean : (n : ℕ) (p : 3 ≤ n) → ∀ x z →
                  Clean (anc (standard n p)) x → (i : Fin (n ∸ 3)) →
                  z (anc (standard n p) i) ≡ true →
                  amp ⟦ ToffoliNᶜ n p ⟧ x z ≐ 0ᴬ
ToffoliNᶜ-clean n p = toffoliNᶜ-clean (standard n p)

ToffoliNᶜ-set0 : (n : ℕ) (p : 3 ≤ n) →
                 set0ˢ (anc (standard n p)) ⟦ ToffoliNᶜ n p ⟧ ≋
                 set0ˢ (anc (standard n p)) (toffoliₙˢ (standard n p))
ToffoliNᶜ-set0 n p = toffoliNᶜ-set0 (standard n p)

ToffoliNᶜ-≋ : (n : ℕ) (p : 3 ≤ n) → ⟦ ToffoliNᶜ n p ⟧ ≋ ⟦ Toffoliₙ n p ⟧
ToffoliNᶜ-≋ n p = toffoliNᶜ-≋ (standard n p)


------------------------------------------------------------------------
-- Resources

private
  -- A count that adds up along a concatenation and is kept by
  -- inversion counts G ++ R ++ G † as G twice and R once ...

  sandwich : (f : Circuit N → ℕ) →
             (∀ C D → f (C ++ D) ≡ f C + f D) → (∀ C → f (C †) ≡ f C) →
             (G R : Circuit N) → f (G ++ R ++ G †) ≡ f G + (f R + f G)
  sandwich f f-++ f-† G R =
    trans (f-++ G (R ++ G †))
          (cong (f G +_) (trans (f-++ R (G †)) (cong (f R +_) (f-† G))))

  -- ... so c per Toffoli gate of the chain adds up to (2j + 1) c.

  step : ∀ c j → c + ((2 * j + 1) * c + c) ≡ (2 * suc j + 1) * c
  step = solve 2 (λ c j → c :+ ((con 2 :* j :+ con 1) :* c :+ c)
                          := (con 2 :* (con 1 :+ j) :+ con 1) :* c) refl

-- Two Hadamards per Toffoli gate, hence two path variables.

toffoliNᶜ-norm : (L : Layout N j) → norm (toffoliNᶜ L) ≡ (2 * j + 1) * 2
toffoliNᶜ-norm {j = zero}  L = refl
toffoliNᶜ-norm {j = suc j} L =
  trans (sandwich norm norm-++ norm-† (subproduct L) (toffoliNᶜ (inner L)))
        (trans (cong (λ m → 2 + (m + 2)) (toffoliNᶜ-norm (inner L)))
               (step 2 j))

toffoliNᶜ-paths : (L : Layout N j) → paths (toffoliNᶜ L) ≡ (2 * j + 1) * 2
toffoliNᶜ-paths L = trans (paths≡norm (toffoliNᶜ L)) (toffoliNᶜ-norm L)

-- Seven T or T† gates per Toffoli gate.

toffoliNᶜ-tcount : (L : Layout N j) → tcount (toffoliNᶜ L) ≡ (2 * j + 1) * 7
toffoliNᶜ-tcount {j = zero}  L = refl
toffoliNᶜ-tcount {j = suc j} L =
  trans (sandwich tcount tcount-++ tcount-† (subproduct L)
                  (toffoliNᶜ (inner L)))
        (trans (cong (λ m → 7 + (m + 7)) (toffoliNᶜ-tcount (inner L)))
               (step 7 j))

-- Nine Clifford gates per Toffoli gate: two Hadamards, seven CNOTs.

toffoliNᶜ-cliffords : (L : Layout N j) →
                      cliffords (toffoliNᶜ L) ≡ (2 * j + 1) * 9
toffoliNᶜ-cliffords {j = zero}  L = refl
toffoliNᶜ-cliffords {j = suc j} L =
  trans (sandwich cliffords cliffords-++ cliffords-† (subproduct L)
                  (toffoliNᶜ (inner L)))
        (trans (cong (λ m → 9 + (m + 9)) (toffoliNᶜ-cliffords (inner L)))
               (step 9 j))

-- On the paper's layout, for every n ≥ 3.

ToffoliNᶜ-paths : (n : ℕ) (p : 3 ≤ n) →
                  paths (ToffoliNᶜ n p) ≡ (2 * (n ∸ 3) + 1) * 2
ToffoliNᶜ-paths n p = toffoliNᶜ-paths (standard n p)

ToffoliNᶜ-tcount : (n : ℕ) (p : 3 ≤ n) →
                   tcount (ToffoliNᶜ n p) ≡ (2 * (n ∸ 3) + 1) * 7
ToffoliNᶜ-tcount n p = toffoliNᶜ-tcount (standard n p)

ToffoliNᶜ-cliffords : (n : ℕ) (p : 3 ≤ n) →
                      cliffords (ToffoliNᶜ n p) ≡ (2 * (n ∸ 3) + 1) * 9
ToffoliNᶜ-cliffords n p = toffoliNᶜ-cliffords (standard n p)


------------------------------------------------------------------------
-- Qubits

-- The circuit touches every control, the target and every ancilla of
-- its layout.  With ancillas, the subproduct touches c₀, c₁ and a₀,
-- and the circuit on the inner layout the rest; without, the one
-- Toffoli circuit touches c₀, c₁ and the target.

private
  in-sub : (L : Layout N (suc j)) {u : Fin N} →
           u ∈ ctl L zero ∷ ctl L (suc zero) ∷ anc L zero ∷ [] →
           u ∈ᶜ toffoliNᶜ L
  in-sub L m =
    ∈ᶜ-++ˡ (subproduct L) (toffoliNᶜ (inner L) ++ subproduct L †)
      (∈ᶜ-tof₃ (ctl L zero) (ctl L (suc zero)) (anc L zero) (c₀≢c₁ L)
               (ctl≢anc L zero zero) (ctl≢anc L (suc zero) zero) m)

  in-inner : (L : Layout N (suc j)) {u : Fin N} →
             u ∈ᶜ toffoliNᶜ (inner L) → u ∈ᶜ toffoliNᶜ L
  in-inner L m =
    ∈ᶜ-++ʳ (subproduct L) (toffoliNᶜ (inner L) ++ subproduct L †)
      (∈ᶜ-++ˡ (toffoliNᶜ (inner L)) (subproduct L †) m)

  in-final : (L : Layout N zero) {u : Fin N} →
             u ∈ ctl L zero ∷ ctl L (suc zero) ∷ tgt L ∷ [] →
             u ∈ᶜ toffoliNᶜ L
  in-final L =
    ∈ᶜ-tof₃ (ctl L zero) (ctl L (suc zero)) (tgt L) (c₀≢c₁ L)
            (ctl≢tgt L zero) (ctl≢tgt L (suc zero))

toffoliNᶜ-ctl : (L : Layout N j) (i : Fin (suc (suc j))) →
                ctl L i ∈ᶜ toffoliNᶜ L
toffoliNᶜ-ctl {j = zero}  L zero          = in-final L (here refl)
toffoliNᶜ-ctl {j = zero}  L (suc zero)    = in-final L (there (here refl))
toffoliNᶜ-ctl {j = zero}  L (suc (suc ()))
toffoliNᶜ-ctl {j = suc j} L zero          = in-sub L (here refl)
toffoliNᶜ-ctl {j = suc j} L (suc zero)    = in-sub L (there (here refl))
toffoliNᶜ-ctl {j = suc j} L (suc (suc i)) =
  in-inner L (toffoliNᶜ-ctl (inner L) (suc i))

toffoliNᶜ-tgt : (L : Layout N j) → tgt L ∈ᶜ toffoliNᶜ L
toffoliNᶜ-tgt {j = zero}  L = in-final L (there (there (here refl)))
toffoliNᶜ-tgt {j = suc j} L = in-inner L (toffoliNᶜ-tgt (inner L))

toffoliNᶜ-anc : (L : Layout N j) (i : Fin j) → anc L i ∈ᶜ toffoliNᶜ L
toffoliNᶜ-anc {j = zero}  L ()
toffoliNᶜ-anc {j = suc j} L zero    = in-sub L (there (there (here refl)))
toffoliNᶜ-anc {j = suc j} L (suc i) =
  in-inner L (toffoliNᶜ-anc (inner L) i)

-- So on a layout that covers its wires every wire is touched, and the
-- circuit's qubits, counted as the tool counts them, are all of them
-- ...

toffoliNᶜ-qubits : (L : Layout N j) → Covers L → qubits (toffoliNᶜ L) ≡ N
toffoliNᶜ-qubits L cov =
  qubits-all (toffoliNᶜ L)
    (covered (_∈ᶜ toffoliNᶜ L) L (toffoliNᶜ-ctl L) (toffoliNᶜ-tgt L)
             (toffoliNᶜ-anc L) cov)

-- ... n + (n − 3) on the paper's layout, for every n ≥ 3.

ToffoliNᶜ-qubits : (n : ℕ) (p : 3 ≤ n) →
                   qubits (ToffoliNᶜ n p) ≡ n + (n ∸ 3)
ToffoliNᶜ-qubits n p = toffoliNᶜ-qubits (standard n p) (standard-wires n p)


------------------------------------------------------------------------
-- Table 2

-- Toffoli50 and Toffoli100, in all four columns: 97 and 197 qubits,
-- 190 and 390 path variables, 855 and 1755 Clifford gates, 665 and
-- 1365 T gates.  (The circuits are not computed: these are the counts
-- above at n = 50 and n = 100.)

Toffoli50ᵀ : (p : 3 ≤ 50) →
             (qubits (ToffoliNᶜ 50 p) ≡ 97)
             × (paths (ToffoliNᶜ 50 p) ≡ 190)
             × (cliffords (ToffoliNᶜ 50 p) ≡ 855)
             × (tcount (ToffoliNᶜ 50 p) ≡ 665)
Toffoli50ᵀ p =
  ToffoliNᶜ-qubits 50 p , ToffoliNᶜ-paths 50 p , ToffoliNᶜ-cliffords 50 p
  , ToffoliNᶜ-tcount 50 p

Toffoli100ᵀ : (p : 3 ≤ 100) →
              (qubits (ToffoliNᶜ 100 p) ≡ 197)
              × (paths (ToffoliNᶜ 100 p) ≡ 390)
              × (cliffords (ToffoliNᶜ 100 p) ≡ 1755)
              × (tcount (ToffoliNᶜ 100 p) ≡ 1365)
Toffoli100ᵀ p =
  ToffoliNᶜ-qubits 100 p , ToffoliNᶜ-paths 100 p
  , ToffoliNᶜ-cliffords 100 p , ToffoliNᶜ-tcount 100 p
