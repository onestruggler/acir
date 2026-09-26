------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H, CNOT, R_k, R_k†} acting on columns: circuits moved
-- to other wires, diagonal circuits, and the phase oracles of the
-- hidden shift algorithm (Amy, QPL 2018, section 5.2)
--
-- Phase B of the hidden shift package turns the path-sums of
-- PathSum.HiddenShift into circuits over the gate set of definition
-- 2.9 (PathSum.CRK.Circuit).  Its plan:
--
--  1. This module: the column algebra of such circuits.  Proposition
--     2.10 (PathSum.CRK.Semantics.prop-2-10) says the amplitudes of
--     ⟦ C ⟧ at x are the gates of C applied in turn to the basis
--     column δ x (applyᴬ), so everything is proved about applyᴬ on
--     columns, never about the polynomials ⟦_⟧ computes.  A circuit on
--     the last n of n + 1 wires acts on each slice of a column with the
--     first bit fixed (applyᴬ-lift), and one on the first k of k + l
--     wires on each slice with the last l bits fixed (applyᴬ-upper).
--     A diagonal circuit multiplies every entry by a power of ζ
--     depending on the entry's index (Diag); diagonal circuits compose
--     (Diag-++) and stay diagonal when conjugated by a CNOT, which
--     moves the phase to the parity of two wires (Diag-conj).  So the
--     gadgets of the paper's oracles are diagonal: Z = R₁ (Zᶜ), CZ from
--     three S gates on the parities a, b, a ⊕ b (CZᶜ), and CCZ from
--     seven T gates on the parities a, b, c, b ⊕ c, a ⊕ b ⊕ c, a ⊕ c,
--     a ⊕ b (CCZᶜ), each multiplying the entry at z by (-1) to the
--     monomial.  A list of monomials of degree at most 3 (Term) is
--     compiled gadget by gadget (oracle) into the diagonal (-1)^{g(z)},
--     g the sum of the monomials over Z₂ (Signs-oracle).
--  2. PathSum.HiddenShift.Layers: the Hadamard layer H^{⊗n}, the
--     X layer X^s, and a simulation relation Sim between operators on
--     columns and path-sums, which composes along definition 2.6.
--  3. PathSum.HiddenShift.Circuit: the Maiorana-McFarland oracles and
--     the circuit of figure 3(a); its path-sum is equivalent to the
--     composite of PathSum.HiddenShift, so on |0⟩ it gives |s⟩.
--  4. PathSum.HiddenShift.Symbolic: figure 3(b), the shift held in a
--     second register, |0⟩|s⟩ ↦ |s⟩|s⟩.
--  5. PathSum.Ancilla.Register: a register of ancillas prepared in
--     |0⟩, extending PathSum.Ancilla from one wire to several.
--  6. PathSum.HiddenShift.Reduces: every complete reduction of figure
--     3(b)'s path-sum by the rules of figure 2 ends at |s⟩|s⟩, as
--     PathSum.HiddenShift.Circuit shows for |s⟩ and figure 3(a).
--  7. PathSum.HiddenShift.CircuitExample: cross-checks at one closed
--     instance, at M₀ = 0.
--
-- Departures from the paper.  The paper's random instances contain
-- "Z and controlled-Z gates, then a random doubly controlled-Z gate,
-- expanded out to Clifford+T" without saying how; here CZ uses three
-- S = R₂ gates and CCZ seven T = R₃ gates, each parity computed by its
-- own CNOTs and uncomputed at once (ten CNOTs for CCZ, where the usual
-- network shares them and needs six).  Only the gates' semantics
-- matter here, and those are exact: the phase of each gadget is ½
-- times the monomial as an integer, not merely modulo 1.  The gate
-- R 3 needs M ≥ 3, which holds for every M₀ (M = M₀ + 3).  Monomials
-- have no constant term, as a Z-gate circuit cannot produce one; a
-- constant in g would be a global sign of both oracles, and cancels.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Gates (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; _↑ˡ_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; divides)
open import Data.Integer.Properties using
  (*-identityˡ; *-identityʳ; *-zeroʳ; +-identityˡ; -1*i≡-i;
   neg-distribˡ-*; *-assoc; *-comm)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Nat.Base using (zero; suc; _∸_) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)

import Data.Fin.Properties as Fin

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-self)
open import PathSum.AssignSum using (_∷ᵃ_)
open import PathSum.CircuitSemantics M₀ using (Column)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; _·ᴬ_; N; rot; rot-map; rot-exp; rot-0; rot-anti; rot-comp;
   coeff-cong; Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Sign M₀ using (½-parity)
open import PathSum.HiddenShift.Walsh using
  (_⧺_; ⧺-↑ˡ; RespectsB; sgn-xor)
open import PathSum.Polynomial using (sgn)
open import PathSum.Polynomial.Bind using (odd)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; :-_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; applyᴬ-++; applyᴬ-cong; applyᴬ-resp; gateᴬ-resp)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Reduction M using (½)

private
  variable
    n k l : ℕ


------------------------------------------------------------------------
-- Signs on any amplitude

-- Rotations by exponents that agree modulo N agree, ζ having order N.
-- The two exponents are compared through Cyclotomic's coeff-cong,
-- never by conversion.

rot-N : ∀ e e′ (a : Amp) → (+ N) ∣ (e - e′) → rot e a ≐ rot e′ a
rot-N e e′ a (divides q eq) i =
  coeff-cong a ((+ toℕ i) - e) ((+ toℕ i) - e′)
    (divides (- q) (trans (shape (+ toℕ i) e e′)
                   (trans (cong -_ eq) (neg-distribˡ-* q (+ N)))))
  where
  shape : ∀ u v w → (u - v) - (u - w) ≡ - (v - w)
  shape = solve 3 (λ u v w → (u :- v) :- (u :- w) := :- (v :- w)) refl

-- ζ^(½ b) is (-1)^b, and so is ζ^(½ v) for any v of parity b.

rot-½-bit : ∀ b (a : Amp) → rot (½ * [ b ]ᶻ) a ≐ sgn b ·ᴬ a
rot-½-bit false a i =
  trans (rot-exp {½ * [ false ]ᶻ} {0ℤ} a (*-zeroʳ ½) i)
        (trans (rot-0 a i) (sym (*-identityˡ (a i))))
rot-½-bit true  a i =
  trans (rot-exp {½ * [ true ]ᶻ} {0ℤ + (+ rank)} a
                 (trans (*-identityʳ ½) (sym (+-identityˡ ½))) i)
    (trans (rot-anti 0ℤ a i)
      (trans (cong -_ (rot-0 a i)) (sym (-1*i≡-i (a i)))))

rot-½ᴬ : ∀ v (a : Amp) → rot (½ * v) a ≐ sgn (odd v) ·ᴬ a
rot-½ᴬ v a i = trans (rot-N (½ * v) (½ * [ odd v ]ᶻ) a (½-parity v) i)
                     (rot-½-bit (odd v) a i)


------------------------------------------------------------------------
-- A circuit moved one wire down

-- The gates of C on n wires, moved to the wires 1 … n of n + 1.

↑g : Gate n → Gate (suc n)
↑g (H w)        = H (suc w)
↑g (CNOT c t p) = CNOT (suc c) (suc t) (λ e → p (Fin.suc-injective e))
↑g (R k w)      = R k (suc w)
↑g (R† k w)     = R† k (suc w)

lift : Circuit n → Circuit (suc n)
lift []      = []
lift (g ∷ C) = ↑g g ∷ lift C

norm-lift : (C : Circuit n) → norm (lift C) ≡ norm C
norm-lift []               = refl
norm-lift (H _ ∷ C)        = cong suc (norm-lift C)
norm-lift (CNOT _ _ _ ∷ C) = norm-lift C
norm-lift (R _ _ ∷ C)      = norm-lift C
norm-lift (R† _ _ ∷ C)     = norm-lift C

-- Comparing two successors is comparing them.

⌊≟⌋-suc : (j w : Fin n) → ⌊ Fin.suc j Fin.≟ suc w ⌋ ≡ ⌊ j Fin.≟ w ⌋
⌊≟⌋-suc j w with j Fin.≟ w
... | yes _ = refl
... | no  _ = refl

-- Overwriting a bit below the head.

∷ᵃ-≔ : (b : Bool) (u : Assign n) (w : Fin n) (c : Bool) →
       ∀ j → ((b ∷ᵃ u) [ suc w ≔ c ]) j ≡ (b ∷ᵃ (u [ w ≔ c ])) j
∷ᵃ-≔ b u w c zero    = refl
∷ᵃ-≔ b u w c (suc j) = cong (λ t → if t then c else u j) (⌊≟⌋-suc j w)

∷ᵃ-cong : (b : Bool) {u u′ : Assign n} → (∀ j → u j ≡ u′ j) →
          ∀ j → (b ∷ᵃ u) j ≡ (b ∷ᵃ u′) j
∷ᵃ-cong b h zero    = refl
∷ᵃ-cong b h (suc j) = h j

-- Every assignment is its head bit followed by its tail.

∷ᵃ-η : (z : Assign (suc n)) → ∀ j → z j ≡ (z zero ∷ᵃ (λ i → z (suc i))) j
∷ᵃ-η z zero    = refl
∷ᵃ-η z (suc j) = refl

-- Slices of a column with the head bit fixed respect pointwise
-- equality.

slice-resp : {ψ : Column (suc n)} → Respects ψ → ∀ b →
             Respects (λ u → ψ (b ∷ᵃ u))
slice-resp resp b u u′ h = resp (b ∷ᵃ u) (b ∷ᵃ u′) (∷ᵃ-cong b h)

-- A moved gate, and so a moved circuit, acts on every slice.

gate-lift : (g : Gate n) {ψ : Column (suc n)} → Respects ψ →
            ∀ b u → gateᴬ (↑g g) ψ (b ∷ᵃ u) ≐ gateᴬ g (λ u′ → ψ (b ∷ᵃ u′)) u
gate-lift (H w) {ψ} resp b u i = cong₂ _+_
  (resp _ _ (∷ᵃ-≔ b u w false) i)
  (rot-map (½ * [ u w ]ᶻ) (resp _ _ (∷ᵃ-≔ b u w true)) i)
gate-lift (CNOT c t p) resp b u = resp _ _ (∷ᵃ-≔ b u t (u t xor u c))
gate-lift (R k w)      resp b u i = refl
gate-lift (R† k w)     resp b u i = refl

applyᴬ-lift : (C : Circuit n) {ψ : Column (suc n)} → Respects ψ →
              ∀ b u → applyᴬ (lift C) ψ (b ∷ᵃ u) ≐
                      applyᴬ C (λ u′ → ψ (b ∷ᵃ u′)) u
applyᴬ-lift []      resp b u i = refl
applyᴬ-lift (g ∷ C) {ψ} resp b u i = trans
  (applyᴬ-lift C (gateᴬ-resp (↑g g) resp) b u i)
  (applyᴬ-cong C {λ u′ → gateᴬ (↑g g) ψ (b ∷ᵃ u′)}
                 {gateᴬ g (λ u′ → ψ (b ∷ᵃ u′))}
                 (gate-lift g resp b) u i)


------------------------------------------------------------------------
-- A circuit on the first block of wires

-- The gates of C on k wires, placed on the first k of k + l.

◂g : ∀ l → Gate k → Gate (k ℕ+ l)
◂g l (H w)        = H (w ↑ˡ l)
◂g l (CNOT c t p) = CNOT (c ↑ˡ l) (t ↑ˡ l)
                         (λ e → p (Fin.↑ˡ-injective l c t e))
◂g l (R k w)      = R k (w ↑ˡ l)
◂g l (R† k w)     = R† k (w ↑ˡ l)

upper : ∀ l → Circuit k → Circuit (k ℕ+ l)
upper l []      = []
upper l (g ∷ C) = ◂g l g ∷ upper l C

norm-upper : ∀ l (C : Circuit k) → norm (upper l C) ≡ norm C
norm-upper l []               = refl
norm-upper l (H _ ∷ C)        = cong suc (norm-upper l C)
norm-upper l (CNOT _ _ _ ∷ C) = norm-upper l C
norm-upper l (R _ _ ∷ C)      = norm-upper l C
norm-upper l (R† _ _ ∷ C)     = norm-upper l C

upper-++ : ∀ l (C D : Circuit k) → upper l (C ++ D) ≡ upper l C ++ upper l D
upper-++ l []      D = refl
upper-++ l (g ∷ C) D = cong (◂g l g ∷_) (upper-++ l C D)

-- Concatenation reads its first block pointwise.

⧺-cong : (a a′ : Assign k) (v : Assign l) → (∀ i → a i ≡ a′ i) →
         ∀ j → (a ⧺ v) j ≡ (a′ ⧺ v) j
⧺-cong {zero}  a a′ v h j       = refl
⧺-cong {suc k} a a′ v h zero    = h zero
⧺-cong {suc k} a a′ v h (suc j) =
  ⧺-cong (λ i → a (suc i)) (λ i → a′ (suc i)) v (λ i → h (suc i)) j

-- Overwriting a bit of the first block.

⧺-≔ : (u : Assign k) (v : Assign l) (i : Fin k) (c : Bool) →
      ∀ j → ((u ⧺ v) [ i ↑ˡ l ≔ c ]) j ≡ ((u [ i ≔ c ]) ⧺ v) j
⧺-≔ {suc k}     u v zero    c zero    = refl
⧺-≔ {suc k}     u v zero    c (suc j) = refl
⧺-≔ {suc k}     u v (suc i) c zero    = refl
⧺-≔ {suc k} {l} u v (suc i) c (suc j) = trans
  (cong (λ t → if t then c else ((λ i′ → u (suc i′)) ⧺ v) j)
        (⌊≟⌋-suc j (i ↑ˡ l)))
  (trans (⧺-≔ (λ i′ → u (suc i′)) v i c j)
         (⧺-cong ((λ i′ → u (suc i′)) [ i ≔ c ])
                 (λ i′ → (u [ suc i ≔ c ]) (suc i′)) v
                 (λ i′ → cong (λ t → if t then c else u (suc i′))
                              (sym (⌊≟⌋-suc i′ i)))
                 j))

-- Slices with the second block fixed respect pointwise equality.

sliceʳ-resp : {ψ : Column (k ℕ+ l)} → Respects ψ → (v : Assign l) →
              Respects (λ (u : Assign k) → ψ (u ⧺ v))
sliceʳ-resp resp v u u′ h = resp (u ⧺ v) (u′ ⧺ v) (⧺-cong u u′ v h)

-- A gate on the first block, and so a circuit, acts on every slice.

gate-upper : ∀ l (g : Gate k) {ψ : Column (k ℕ+ l)} → Respects ψ →
             (u : Assign k) (v : Assign l) → gateᴬ (◂g l g) ψ (u ⧺ v) ≐
                     gateᴬ g (λ u′ → ψ (u′ ⧺ v)) u
gate-upper l (H w) {ψ} resp u v i = cong₂ _+_
  (resp _ _ (⧺-≔ u v w false) i)
  (trans (rot-exp {½ * [ (u ⧺ v) (w ↑ˡ l) ]ᶻ} {½ * [ u w ]ᶻ}
                  (ψ ((u ⧺ v) [ w ↑ˡ l ≔ true ]))
                  (cong (λ b → ½ * [ b ]ᶻ) (⧺-↑ˡ u v w)) i)
         (rot-map (½ * [ u w ]ᶻ) (resp _ _ (⧺-≔ u v w true)) i))
gate-upper l (CNOT c t p) {ψ} resp u v = resp _ _ (λ j → trans
  (cong (λ b → ((u ⧺ v) [ t ↑ˡ l ≔ b ]) j)
        (cong₂ _xor_ (⧺-↑ˡ u v t) (⧺-↑ˡ u v c)))
  (⧺-≔ u v t (u t xor u c) j))
gate-upper l (R k w) {ψ} resp u v =
  rot-exp {pow (M ∸ k) * [ (u ⧺ v) (w ↑ˡ l) ]ᶻ} {pow (M ∸ k) * [ u w ]ᶻ}
          (ψ (u ⧺ v)) (cong (λ b → pow (M ∸ k) * [ b ]ᶻ) (⧺-↑ˡ u v w))
gate-upper l (R† k w) {ψ} resp u v =
  rot-exp { - (pow (M ∸ k) * [ (u ⧺ v) (w ↑ˡ l) ]ᶻ)}
          { - (pow (M ∸ k) * [ u w ]ᶻ)}
          (ψ (u ⧺ v)) (cong (λ b → - (pow (M ∸ k) * [ b ]ᶻ)) (⧺-↑ˡ u v w))

applyᴬ-upper : ∀ l (C : Circuit k) {ψ : Column (k ℕ+ l)} → Respects ψ →
               (u : Assign k) (v : Assign l) → applyᴬ (upper l C) ψ (u ⧺ v) ≐
                       applyᴬ C (λ u′ → ψ (u′ ⧺ v)) u
applyᴬ-upper l []      resp u v i = refl
applyᴬ-upper l (g ∷ C) {ψ} resp u v i = trans
  (applyᴬ-upper l C (gateᴬ-resp (◂g l g) resp) u v i)
  (applyᴬ-cong C {λ u′ → gateᴬ (◂g l g) ψ (u′ ⧺ v)}
                 {gateᴬ g (λ u′ → ψ (u′ ⧺ v))}
                 (λ u′ → gate-upper l g resp u′ v) u i)


------------------------------------------------------------------------
-- Diagonal circuits

-- C multiplies the entry at z of every column by ζ^(φ z).

record Diag (C : Circuit n) (φ : Assign n → ℤ) : Set where
  constructor diag
  field
    diagonal : (ψ : Column n) → Respects ψ →
               ∀ z → applyᴬ C ψ z ≐ rot (φ z) (ψ z)

open Diag public

-- The phase gates.

Diag-R : (k : ℕ) (w : Fin n) →
         Diag (R k w ∷ []) (λ z → pow (M ∸ k) * [ z w ]ᶻ)
Diag-R k w = diag (λ ψ _ z _ → refl)

Diag-R† : (k : ℕ) (w : Fin n) →
          Diag (R† k w ∷ []) (λ z → - (pow (M ∸ k) * [ z w ]ᶻ))
Diag-R† k w = diag (λ ψ _ z _ → refl)

-- Phases add up.

Diag-++ : {C D : Circuit n} {φ χ : Assign n → ℤ} →
          Diag C φ → Diag D χ → Diag (C ++ D) (λ z → χ z + φ z)
Diag-++ {C = C} {D} {φ} {χ} dC dD = diag λ ψ r z i →
  trans (cong (λ F → F z i) (applyᴬ-++ C D ψ))
    (trans (diagonal dD (applyᴬ C ψ) (applyᴬ-resp C r) z i)
      (trans (rot-map (χ z) (diagonal dC ψ r z) i)
             (rot-comp (χ z) (φ z) (ψ z) i)))

-- A CNOT and its inverse around a diagonal circuit: the circuit now
-- reads the target as the parity of target and control.

private
  xor-cancel : ∀ a b → (a xor b) xor b ≡ a
  xor-cancel false false = refl
  xor-cancel false true  = refl
  xor-cancel true  false = refl
  xor-cancel true  true  = refl

cnot-twice : (z : Assign n) {c t : Fin n} → c ≢ t → ∀ j →
             ((z [ t ≔ z t xor z c ]) [ t ≔ (z [ t ≔ z t xor z c ]) t xor
                                             (z [ t ≔ z t xor z c ]) c ]) j ≡
             z j
cnot-twice z {c} {t} p j = trans
  (cong (λ b → ((z [ t ≔ z t xor z c ]) [ t ≔ b ]) j)
        (trans (cong₂ _xor_ (≔-here z t (z t xor z c))
                            (≔-there z (z t xor z c) p))
               (xor-cancel (z t) (z c))))
  (trans (≔-≔ z t (z t xor z c) (z t) j) (≔-self z t j))

Diag-conj : (c t : Fin n) (p : c ≢ t) {D : Circuit n} {χ : Assign n → ℤ} →
            Diag D χ →
            Diag (CNOT c t p ∷ D ++ CNOT c t p ∷ [])
                 (λ z → χ (z [ t ≔ z t xor z c ]))
Diag-conj c t p {D} {χ} dD = diag λ ψ r z i →
  trans (cong (λ F → F z i)
              (applyᴬ-++ D (CNOT c t p ∷ []) (gateᴬ (CNOT c t p) ψ)))
    (trans (diagonal dD (gateᴬ (CNOT c t p) ψ) (gateᴬ-resp (CNOT c t p) r)
                     (z [ t ≔ z t xor z c ]) i)
           (rot-map (χ (z [ t ≔ z t xor z c ]))
                    (r _ z (cnot-twice z p)) i))

-- The exponent may be rewritten.

Diag-cong : {C : Circuit n} {φ φ′ : Assign n → ℤ} →
            Diag C φ → (∀ z → φ z ≡ φ′ z) → Diag C φ′
Diag-cong {φ = φ} {φ′} d h = diag λ ψ r z i →
  trans (diagonal d ψ r z i) (rot-exp {φ z} {φ′ z} (ψ z) (h z) i)


------------------------------------------------------------------------
-- The phase gadgets

-- Z = R₁: ζ^(½ z_a).

Zᶜ : Fin n → Circuit n
Zᶜ a = R 1 a ∷ []

-- The phase -2^(M-k) (z_t ⊕ z_c) on the target t, and 2^(M-k)
-- (z_c ⊕ z_a ⊕ z_b) on c.

par⁻ : ℕ → (c t : Fin n) → c ≢ t → Circuit n
par⁻ k c t p = CNOT c t p ∷ R† k t ∷ CNOT c t p ∷ []

par⁺ : ℕ → (a b c : Fin n) → a ≢ c → b ≢ c → Circuit n
par⁺ k a b c q r =
  CNOT a c q ∷ CNOT b c r ∷ R k c ∷ CNOT b c r ∷ CNOT a c q ∷ []

-- CZ from S = R₂ on a, b and (inversely) on a ⊕ b.

CZᶜ : (a b : Fin n) → a ≢ b → Circuit n
CZᶜ a b p = R 2 a ∷ R 2 b ∷ par⁻ 2 a b p

-- CCZ from T = R₃ on a, b, c, a ⊕ b ⊕ c, and inversely on b ⊕ c,
-- a ⊕ c, a ⊕ b.

CCZᶜ : (a b c : Fin n) → a ≢ b → a ≢ c → b ≢ c → Circuit n
CCZᶜ a b c p q r = R 3 a ∷ R 3 b ∷ R 3 c ∷
  (par⁻ 3 b c r ++ (par⁺ 3 a b c q r ++ (par⁻ 3 a c q ++ par⁻ 3 a b p)))

-- Their phases, as integers.

private
  xor-bits : ∀ a b → [ b xor a ]ᶻ ≡ ([ a ]ᶻ + [ b ]ᶻ) - (+ 2) * [ a ∧ b ]ᶻ
  xor-bits false false = refl
  xor-bits false true  = refl
  xor-bits true  false = refl
  xor-bits true  true  = refl

  and-bits : ∀ a b c →
    ((((((- [ b xor a ]ᶻ) + (- [ c xor a ]ᶻ)) + [ (c xor a) xor b ]ᶻ) +
       (- [ c xor b ]ᶻ)) + [ c ]ᶻ) + [ b ]ᶻ) + [ a ]ᶻ ≡
    (+ 4) * [ a ∧ (b ∧ c) ]ᶻ
  and-bits false false false = refl
  and-bits false false true  = refl
  and-bits false true  false = refl
  and-bits false true  true  = refl
  and-bits true  false false = refl
  and-bits true  false true  = refl
  and-bits true  true  false = refl
  and-bits true  true  true  = refl

  -- ¼ + ¼ = ½ and ⅛ · 4 = ½.

  ¼·2 : pow (suc M₀) * (+ 2) ≡ ½
  ¼·2 = sym (pow-suc (suc M₀))

  ⅛·4 : pow M₀ * (+ 4) ≡ ½
  ⅛·4 = trans (shape (pow M₀))
    (trans (cong (_* (+ 2)) (sym (pow-suc M₀))) ¼·2)
    where
    shape : ∀ q → q * (+ 4) ≡ (q * (+ 2)) * (+ 2)
    shape = solve 1 (λ q → q :* con (+ 4) := (q :* con (+ 2)) :* con (+ 2))
                    refl

  cz-exp : ∀ a b →
           (- (pow (suc M₀) * [ b xor a ]ᶻ) + pow (suc M₀) * [ b ]ᶻ) +
             pow (suc M₀) * [ a ]ᶻ ≡ ½ * [ a ∧ b ]ᶻ
  cz-exp a b = trans
    (cong (λ X → (- (q * X) + q * [ b ]ᶻ) + q * [ a ]ᶻ) (xor-bits a b))
    (trans (shape q [ a ]ᶻ [ b ]ᶻ [ a ∧ b ]ᶻ)
           (cong (_* [ a ∧ b ]ᶻ) ¼·2))
    where
    q : ℤ
    q = pow (suc M₀)

    shape : ∀ q A B C →
            (- (q * ((A + B) - (+ 2) * C)) + q * B) + q * A ≡ (q * (+ 2)) * C
    shape = solve 4 (λ q A B C →
      (:- (q :* ((A :+ B) :- con (+ 2) :* C)) :+ q :* B) :+ q :* A :=
      (q :* con (+ 2)) :* C) refl

  ccz-exp : ∀ a b c →
    ((((((- (pow M₀ * [ b xor a ]ᶻ)) + (- (pow M₀ * [ c xor a ]ᶻ))) +
          pow M₀ * [ (c xor a) xor b ]ᶻ) + (- (pow M₀ * [ c xor b ]ᶻ))) +
       pow M₀ * [ c ]ᶻ) + pow M₀ * [ b ]ᶻ) + pow M₀ * [ a ]ᶻ ≡
    ½ * [ a ∧ (b ∧ c) ]ᶻ
  ccz-exp a b c = trans
    (shape (pow M₀) [ b xor a ]ᶻ [ c xor a ]ᶻ [ (c xor a) xor b ]ᶻ
           [ c xor b ]ᶻ [ c ]ᶻ [ b ]ᶻ [ a ]ᶻ)
    (trans (cong (pow M₀ *_) (and-bits a b c))
      (trans (sym (*-assoc (pow M₀) (+ 4) [ a ∧ (b ∧ c) ]ᶻ))
             (cong (_* [ a ∧ (b ∧ c) ]ᶻ) ⅛·4)))
    where
    shape : ∀ q A B C D E F G →
      ((((((- (q * A)) + (- (q * B))) + q * C) + (- (q * D))) + q * E) +
         q * F) + q * G ≡
      q * ((((((- A + - B) + C) + - D) + E) + F) + G)
    shape = solve 8 (λ q A B C D E F G →
      ((((((:- (q :* A)) :+ (:- (q :* B))) :+ q :* C) :+ (:- (q :* D))) :+
          q :* E) :+ q :* F) :+ q :* G :=
      q :* ((((((:- A :+ :- B) :+ C) :+ :- D) :+ E) :+ F) :+ G)) refl

-- Each gadget multiplies the entry at z by ζ^(½ m(z)), m its monomial.

Diag-Z : (a : Fin n) → Diag (Zᶜ a) (λ z → ½ * [ z a ]ᶻ)
Diag-Z a = Diag-R 1 a

Diag-par⁻ : (k : ℕ) (c t : Fin n) (p : c ≢ t) →
            Diag (par⁻ k c t p)
                 (λ z → - (pow (M ∸ k) * [ (z [ t ≔ z t xor z c ]) t ]ᶻ))
Diag-par⁻ k c t p = Diag-conj c t p (Diag-R† k t)

Diag-par⁺ : (k : ℕ) (a b c : Fin n) (q : a ≢ c) (r : b ≢ c) →
            Diag (par⁺ k a b c q r)
                 (λ z → pow (M ∸ k) *
                          [ ((z [ c ≔ z c xor z a ]) [ c ≔
                               (z [ c ≔ z c xor z a ]) c xor
                               (z [ c ≔ z c xor z a ]) b ]) c ]ᶻ)
Diag-par⁺ k a b c q r = Diag-conj a c q (Diag-conj b c r (Diag-R k c))

Diag-CZ : (a b : Fin n) (p : a ≢ b) →
          Diag (CZᶜ a b p) (λ z → ½ * [ z a ∧ z b ]ᶻ)
Diag-CZ a b p = Diag-cong
  (Diag-++ (Diag-R 2 a) (Diag-++ (Diag-R 2 b) (Diag-par⁻ 2 a b p)))
  (λ z → trans
    (cong (λ t → (- (pow (suc M₀) * [ t ]ᶻ) + pow (suc M₀) * [ z b ]ᶻ) +
                 pow (suc M₀) * [ z a ]ᶻ)
          (≔-here z b (z b xor z a)))
    (cz-exp (z a) (z b)))

Diag-CCZ : (a b c : Fin n) (p : a ≢ b) (q : a ≢ c) (r : b ≢ c) →
           Diag (CCZᶜ a b c p q r) (λ z → ½ * [ z a ∧ (z b ∧ z c) ]ᶻ)
Diag-CCZ a b c p q r = Diag-cong
  (Diag-++ (Diag-R 3 a) (Diag-++ (Diag-R 3 b) (Diag-++ (Diag-R 3 c)
    (Diag-++ (Diag-par⁻ 3 b c r) (Diag-++ (Diag-par⁺ 3 a b c q r)
      (Diag-++ (Diag-par⁻ 3 a c q) (Diag-par⁻ 3 a b p)))))))
  (λ z → trans (bits z) (ccz-exp (z a) (z b) (z c)))
  where
  -- The exponent, as a function of the four parities it reads.
  F : Assign _ → Bool → Bool → Bool → Bool → ℤ
  F z t₁ t₂ t₃ t₄ =
    ((((((- (pow M₀ * [ t₁ ]ᶻ)) + (- (pow M₀ * [ t₂ ]ᶻ))) +
        pow M₀ * [ t₃ ]ᶻ) + (- (pow M₀ * [ t₄ ]ᶻ))) +
      pow M₀ * [ z c ]ᶻ) + pow M₀ * [ z b ]ᶻ) + pow M₀ * [ z a ]ᶻ

  z₅ : Assign _ → Assign _
  z₅ z = z [ c ≔ z c xor z a ]

  abc : ∀ z → ((z₅ z) [ c ≔ z₅ z c xor z₅ z b ]) c ≡ (z c xor z a) xor z b
  abc z = trans (≔-here (z₅ z) c (z₅ z c xor z₅ z b))
    (cong₂ _xor_ (≔-here z c (z c xor z a)) (≔-there z (z c xor z a) r))

  bits : ∀ z →
    F z ((z [ b ≔ z b xor z a ]) b) ((z [ c ≔ z c xor z a ]) c)
        (((z₅ z) [ c ≔ z₅ z c xor z₅ z b ]) c) ((z [ c ≔ z c xor z b ]) c) ≡
    F z (z b xor z a) (z c xor z a) ((z c xor z a) xor z b) (z c xor z b)
  bits z = trans
    (cong₂ (λ t₁ t₂ → F z t₁ t₂ (((z₅ z) [ c ≔ z₅ z c xor z₅ z b ]) c)
                                ((z [ c ≔ z c xor z b ]) c))
           (≔-here z b (z b xor z a)) (≔-here z c (z c xor z a)))
    (cong₂ (λ t₃ t₄ → F z (z b xor z a) (z c xor z a) t₃ t₄)
           (abc z) (≔-here z c (z c xor z b)))


------------------------------------------------------------------------
-- Signs

-- C multiplies the entry at z of every column by (-1)^(b z).

record Signs (C : Circuit n) (b : Assign n → Bool) : Set where
  constructor signs
  field
    signed : (ψ : Column n) → Respects ψ →
             ∀ z → applyᴬ C ψ z ≐ sgn (b z) ·ᴬ ψ z

open Signs public

-- A phase ½ b is the sign of b.

Diag⇒Signs : {C : Circuit n} {b : Assign n → Bool} →
             Diag C (λ z → ½ * [ b z ]ᶻ) → Signs C b
Diag⇒Signs {b = b} d = signs λ ψ r z i →
  trans (diagonal d ψ r z i) (rot-½-bit (b z) (ψ z) i)

-- The empty circuit, concatenation, and rewriting the exponent.

Signs-[] : Signs {n} [] (λ _ → false)
Signs-[] = signs λ ψ r z i → sym (*-identityˡ (ψ z i))

Signs-++ : {C D : Circuit n} {b b′ : Assign n → Bool} →
           Signs C b → Signs D b′ → Signs (C ++ D) (λ z → b z xor b′ z)
Signs-++ {C = C} {D} {b} {b′} sC sD = signs λ ψ r z i →
  trans (cong (λ F → F z i) (applyᴬ-++ C D ψ))
    (trans (signed sD (applyᴬ C ψ) (applyᴬ-resp C r) z i)
      (trans (cong (sgn (b′ z) *_) (signed sC ψ r z i))
        (trans (sym (*-assoc (sgn (b′ z)) (sgn (b z)) (ψ z i)))
               (cong (_* ψ z i)
                     (trans (*-comm (sgn (b′ z)) (sgn (b z)))
                            (sym (sgn-xor (b z) (b′ z))))))))

Signs-cong : {C : Circuit n} {b b′ : Assign n → Bool} →
             Signs C b → (∀ z → b z ≡ b′ z) → Signs C b′
Signs-cong s h = signs λ ψ r z i →
  trans (signed s ψ r z i) (cong (λ t → sgn t * ψ z i) (h z))


------------------------------------------------------------------------
-- Monomials and oracles

-- A monomial of degree 1, 2 or 3 in distinct variables, named after
-- the gate that realises its sign.

data Term (n : ℕ) : Set where
  Z   : Fin n → Term n
  CZ  : (a b : Fin n) → a ≢ b → Term n
  CCZ : (a b c : Fin n) → a ≢ b → a ≢ c → b ≢ c → Term n

-- Its value, and the sum over Z₂ of a list of them.

mono : Term n → Assign n → Bool
mono (Z a)             z = z a
mono (CZ a b _)        z = z a ∧ z b
mono (CCZ a b c _ _ _) z = z a ∧ (z b ∧ z c)

sumᵇ : List (Term n) → Assign n → Bool
sumᵇ []       z = false
sumᵇ (t ∷ ts) z = mono t z xor sumᵇ ts z

mono-resp : (t : Term n) → RespectsB (mono t)
mono-resp (Z a)             u v h = h a
mono-resp (CZ a b _)        u v h = cong₂ _∧_ (h a) (h b)
mono-resp (CCZ a b c _ _ _) u v h = cong₂ _∧_ (h a) (cong₂ _∧_ (h b) (h c))

sumᵇ-resp : (ts : List (Term n)) → RespectsB (sumᵇ ts)
sumᵇ-resp []       u v h = refl
sumᵇ-resp (t ∷ ts) u v h = cong₂ _xor_ (mono-resp t u v h) (sumᵇ-resp ts u v h)

sumᵇ-++ : (ts us : List (Term n)) (z : Assign n) →
          sumᵇ (ts ++ us) z ≡ sumᵇ ts z xor sumᵇ us z
sumᵇ-++ []       us z = refl
sumᵇ-++ (t ∷ ts) us z = trans (cong (mono t z xor_) (sumᵇ-++ ts us z))
  (sym (assoc (mono t z) (sumᵇ ts z) (sumᵇ us z)))
  where
  assoc : ∀ a b c → (a xor b) xor c ≡ a xor (b xor c)
  assoc false b c = refl
  assoc true  false c = refl
  assoc true  true  false = refl
  assoc true  true  true  = refl

-- The circuit of a monomial, and of a list of them.

termᶜ : Term n → Circuit n
termᶜ (Z a)             = Zᶜ a
termᶜ (CZ a b p)        = CZᶜ a b p
termᶜ (CCZ a b c p q r) = CCZᶜ a b c p q r

oracle : List (Term n) → Circuit n
oracle []       = []
oracle (t ∷ ts) = termᶜ t ++ oracle ts

oracle-++ : (ts us : List (Term n)) → oracle (ts ++ us) ≡ oracle ts ++ oracle us
oracle-++ []       us = refl
oracle-++ (t ∷ ts) us = trans (cong (termᶜ t ++_) (oracle-++ ts us))
  (sym (++-assoc (termᶜ t) (oracle ts) (oracle us)))
  where
  ++-assoc : (A B C : Circuit n) → (A ++ B) ++ C ≡ A ++ (B ++ C)
  ++-assoc []      B C = refl
  ++-assoc (g ∷ A) B C = cong (g ∷_) (++-assoc A B C)

-- An oracle has no Hadamard.

norm-oracle : (ts : List (Term n)) → norm (oracle ts) ≡ 0
norm-oracle []                     = refl
norm-oracle (Z _ ∷ ts)             = norm-oracle ts
norm-oracle (CZ _ _ _ ∷ ts)        = norm-oracle ts
norm-oracle (CCZ _ _ _ _ _ _ ∷ ts) = norm-oracle ts

-- The oracle of a list of monomials is the diagonal (-1)^{g(z)}, g
-- their sum.

Signs-term : (t : Term n) → Signs (termᶜ t) (mono t)
Signs-term (Z a)             = Diag⇒Signs (Diag-Z a)
Signs-term (CZ a b p)        = Diag⇒Signs (Diag-CZ a b p)
Signs-term (CCZ a b c p q r) = Diag⇒Signs (Diag-CCZ a b c p q r)

Signs-oracle : (ts : List (Term n)) → Signs (oracle ts) (sumᵇ ts)
Signs-oracle []       = Signs-[]
Signs-oracle (t ∷ ts) = Signs-++ (Signs-term t) (Signs-oracle ts)

-- Monomials moved along an injection of the wires.

mapTerm : (ρ : Fin n → Fin k) → (∀ {a b} → ρ a ≡ ρ b → a ≡ b) →
          Term n → Term k
mapTerm ρ inj (Z a)             = Z (ρ a)
mapTerm ρ inj (CZ a b p)        = CZ (ρ a) (ρ b) (λ e → p (inj e))
mapTerm ρ inj (CCZ a b c p q r) =
  CCZ (ρ a) (ρ b) (ρ c) (λ e → p (inj e)) (λ e → q (inj e))
      (λ e → r (inj e))

sumᵇ-map : (ρ : Fin n → Fin k) (inj : ∀ {a b} → ρ a ≡ ρ b → a ≡ b)
           (ts : List (Term n)) (z : Assign k) →
           sumᵇ (map (mapTerm ρ inj) ts) z ≡ sumᵇ ts (λ i → z (ρ i))
sumᵇ-map ρ inj []                      z = refl
sumᵇ-map ρ inj (Z a ∷ ts)              z =
  cong (z (ρ a) xor_) (sumᵇ-map ρ inj ts z)
sumᵇ-map ρ inj (CZ a b p ∷ ts)         z =
  cong ((z (ρ a) ∧ z (ρ b)) xor_) (sumᵇ-map ρ inj ts z)
sumᵇ-map ρ inj (CCZ a b c p q r ∷ ts)  z =
  cong ((z (ρ a) ∧ (z (ρ b) ∧ z (ρ c))) xor_) (sumᵇ-map ρ inj ts z)
