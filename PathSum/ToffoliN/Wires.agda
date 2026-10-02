------------------------------------------------------------------------
-- Presentations of groups
--
-- The wires of the standard n-bit Toffoli decomposition: its netlist
-- touches every wire of its layout, and the paper's layout leaves no
-- wire out (Amy, QPL 2018, table 2)
--
-- Table 2's first column counts qubits as the paper's tool does: the
-- wires some gate of the circuit touches (PathSum.CRK.Qubits.qubits; a
-- Hadamard or a phase gate touches its wire, a CNOT its control and
-- its target).  For the standard decomposition of PathSum.ToffoliN,
-- and for the tool's own circuit (PathSum.ToffoliN.Tool), that count
-- is every wire of the paper's layout, n + (n − 3) of them.  This
-- module holds the facts those proofs rest on:
--
-- * a Toffoli netlist touches the wires of its gates (_∈ᴺ_), and its
--   expansion into PathSum.Toffoli's seven-T circuit touches the same
--   wires (∈ᶜ-expandᴺ, by PathSum.CRK.Qubits.∈ᶜ-tof);
--
-- * the V-chain of PathSum.ToffoliN.Chain touches every control, the
--   target and every ancilla of its layout (chain-ctl, chain-tgt,
--   chain-anc: the first gate a₀ ⊕= c₀ c₁ touches c₀, c₁ and a₀, and
--   the inner chain the rest; without ancillas the one gate touches
--   c₀, c₁ and the target);
--
-- * a layout covers its wires (Covers) when every wire is a control,
--   the target or an ancilla, and then whatever holds of those holds
--   of every wire (covered); the paper's layout covers its
--   n + (n − 3) wires -- controls 0 … n − 2, target n − 1, ancillas
--   from n on (standard-wires; by Fin's splitAt at the first n wires,
--   each of those being the last or below it, last-or-inject₁).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.ToffoliN.Wires (M₀ : ℕ) where

open import Data.Fin.Base using (Fin; zero; suc; fromℕ; inject₁; splitAt)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat.Base using (_+_; _≤_; z≤n; s≤s)
open import Data.Product.Base using (∃; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; cong)

import Data.Fin.Properties as Fin
import Data.List.Relation.Unary.Any.Properties as Any

open import PathSum.CRK.Qubits M₀ using (_∈ᶜ_; ∈ᶜ-++ˡ; ∈ᶜ-++ʳ; ∈ᶜ-tof)
open import PathSum.Toffoli M₀ using (tof)
open import PathSum.Toffoli.Netlist M₀ using (Toff; toff; expand)
open import PathSum.ToffoliN.Chain M₀ using
  (Layout; ctl; tgt; anc; inner; first; chain; standard)

private
  variable
    n N j k : ℕ


------------------------------------------------------------------------
-- The wires of a Toffoli netlist

-- A Toffoli gate's wires: its two controls and its target.

wiresᴺ : Toff n → List (Fin n)
wiresᴺ g = Toff.c₁ g ∷ Toff.c₂ g ∷ Toff.t g ∷ []

-- u is a wire of some gate of the netlist.

infix 4 _∈ᴺ_

_∈ᴺ_ : Fin n → List (Toff n) → Set
u ∈ᴺ gs = Any (λ g → u ∈ wiresᴺ g) gs

-- The expansion into the seven-T circuit touches the wires of every
-- gate of the netlist.

∈ᶜ-expandᴺ : (gs : List (Toff n)) {u : Fin n} → u ∈ᴺ gs → u ∈ᶜ expand gs
∈ᶜ-expandᴺ (toff c₁ c₂ t p q r ∷ gs) (here m)  =
  ∈ᶜ-++ˡ (tof c₁ c₂ t p q r) (expand gs) (∈ᶜ-tof c₁ c₂ t p q r m)
∈ᶜ-expandᴺ (toff c₁ c₂ t p q r ∷ gs) (there m) =
  ∈ᶜ-++ʳ (tof c₁ c₂ t p q r) (expand gs) (∈ᶜ-expandᴺ gs m)


------------------------------------------------------------------------
-- The chain touches every wire of its layout

-- The inner chain sits between the two copies of the first gate.

private
  in-inner : (L : Layout N (suc j)) {u : Fin N} →
             u ∈ᴺ chain (inner L) → u ∈ᴺ chain L
  in-inner L p =
    there (Any.++⁺ˡ {xs = chain (inner L)} {ys = first L ∷ []} p)

-- The controls: c₀ and c₁ by the first gate (or by the only one), the
-- others, which are the inner layout's, by the inner chain.

chain-ctl : (L : Layout N j) (i : Fin (suc (suc j))) → ctl L i ∈ᴺ chain L
chain-ctl {j = zero}  L zero          = here (here refl)
chain-ctl {j = zero}  L (suc zero)    = here (there (here refl))
chain-ctl {j = zero}  L (suc (suc ()))
chain-ctl {j = suc j} L zero          = here (here refl)
chain-ctl {j = suc j} L (suc zero)    = here (there (here refl))
chain-ctl {j = suc j} L (suc (suc i)) =
  in-inner L (chain-ctl (inner L) (suc i))

-- The target: by the only gate, or by the inner chain.

chain-tgt : (L : Layout N j) → tgt L ∈ᴺ chain L
chain-tgt {j = zero}  L = here (there (there (here refl)))
chain-tgt {j = suc j} L = in-inner L (chain-tgt (inner L))

-- The ancillas: a₀ by the first gate, the others by the inner chain.

chain-anc : (L : Layout N j) (i : Fin j) → anc L i ∈ᴺ chain L
chain-anc {j = zero}  L ()
chain-anc {j = suc j} L zero    = here (there (there (here refl)))
chain-anc {j = suc j} L (suc i) = in-inner L (chain-anc (inner L) i)


------------------------------------------------------------------------
-- Layouts that cover their wires

-- Every wire is a control, the target or an ancilla.

Covers : Layout N j → Set
Covers {N} L = (u : Fin N) →
               (∃ λ i → u ≡ ctl L i) ⊎ u ≡ tgt L ⊎ (∃ λ i → u ≡ anc L i)

-- Then what holds of the controls, the target and the ancillas holds of
-- every wire.

covered : (P : Fin N → Set) (L : Layout N j) →
          (∀ i → P (ctl L i)) → P (tgt L) → (∀ i → P (anc L i)) →
          Covers L → ∀ u → P u
covered P L pc pt pa cov u = go (cov u)
  where
  go : (∃ λ i → u ≡ ctl L i) ⊎ u ≡ tgt L ⊎ (∃ λ i → u ≡ anc L i) → P u
  go (inj₁ (i , refl))        = pc i
  go (inj₂ (inj₁ refl))       = pt
  go (inj₂ (inj₂ (i , refl))) = pa i

-- So the chain touches every wire of a layout that covers its wires.

chain-touched : (L : Layout N j) → Covers L → ∀ u → u ∈ᴺ chain L
chain-touched L =
  covered (_∈ᴺ chain L) L (chain-ctl L) (chain-tgt L) (chain-anc L)


------------------------------------------------------------------------
-- The paper's layout covers its wires

-- A wire of Fin (k + 1) is the last one, k, or one below it.

last-or-inject₁ : (v : Fin (suc k)) → v ≡ fromℕ k ⊎ ∃ λ i → v ≡ inject₁ i
last-or-inject₁ {zero}  zero     = inj₁ refl
last-or-inject₁ {zero}  (suc ())
last-or-inject₁ {suc k} zero     = inj₂ (zero , refl)
last-or-inject₁ {suc k} (suc v)  with last-or-inject₁ v
... | inj₁ e       = inj₁ (cong suc e)
... | inj₂ (i , e) = inj₂ (suc i , cong suc e)

-- For every n ≥ 3, on n + (n − 3) wires: every wire is a control
-- (wires 0 … n − 2), the target (wire n − 1) or an ancilla (the wires
-- from n on).

standard-wires : (n : ℕ) (p : 3 ≤ n) → Covers (standard n p)
standard-wires (suc (suc (suc j))) (s≤s (s≤s (s≤s z≤n))) u =
  go (splitAt (suc (suc (suc j))) u) refl
  where
  L : Layout (suc (suc (suc j)) + j) j
  L = standard (suc (suc (suc j))) (s≤s (s≤s (s≤s z≤n)))

  go : (s : Fin (suc (suc (suc j))) ⊎ Fin j) →
       splitAt (suc (suc (suc j))) u ≡ s →
       (∃ λ i → u ≡ ctl L i) ⊎ u ≡ tgt L ⊎ (∃ λ i → u ≡ anc L i)
  go (inj₁ v) e with last-or-inject₁ v
  ... | inj₁ refl       = inj₂ (inj₁ (sym (Fin.splitAt⁻¹-↑ˡ e)))
  ... | inj₂ (i , refl) = inj₁ (i , sym (Fin.splitAt⁻¹-↑ˡ e))
  go (inj₂ i) e = inj₂ (inj₂ (i , sym (Fin.splitAt⁻¹-↑ʳ e)))
